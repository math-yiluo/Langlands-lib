import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardLeviConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCenterHeightProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LaurentExponent
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Height bounds for the actual unitary Laurent coordinates -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

private theorem norm_pi_int_cast {I : Type*} [Fintype I] (x : I → ℤ) :
    ‖fun j => (x j : ℝ)‖ = ‖x‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun j => by
      rw [Int.norm_cast_real]
      exact norm_le_pi_norm x j
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg (fun j => (x j : ℝ)))).mpr fun j => by
      rw [← Int.norm_cast_real]
      exact norm_le_pi_norm (fun j => (x j : ℝ)) j

/-- An injective integer-linear map between finite coordinate lattices
controls the sup norm via its real linear extension. -/
private theorem exists_norm_le_of_int_linear_injective {I J : Type*} [Fintype I] [Fintype J]
    (T : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (hT : Function.Injective T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖x‖ ≤ C * ‖T x‖ := by
  classical
  let eJ := TensorProduct.piScalarRight ℤ ℝ ℝ J
  let eI := TensorProduct.piScalarRight ℤ ℝ ℝ I
  let R : (J → ℝ) →ₗ[ℝ] (I → ℝ) :=
    eI.toLinearMap ∘ₗ T.baseChange ℝ ∘ₗ eJ.symm.toLinearMap
  have hinj : Function.Injective R :=
    eI.injective.comp ((Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) T hT).comp
      eJ.symm.injective)
  obtain ⟨L, hL⟩ := R.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  let Lc := L.toContinuousLinearMap
  refine ⟨‖Lc‖, norm_nonneg _, fun x => ?_⟩
  have hJ : eJ ((1 : ℝ) ⊗ₜ[ℤ] x) = fun j => (x j : ℝ) := by
    simp [eJ, zsmul_eq_mul]
  have hI : eI ((1 : ℝ) ⊗ₜ[ℤ] T x) = fun i => (T x i : ℝ) := by
    simp [eI, zsmul_eq_mul]
  have hR : R (fun j => (x j : ℝ)) = fun i => (T x i : ℝ) := by
    rw [← hJ, ← hI]
    simp [R]
  have hx : Lc (fun i => (T x i : ℝ)) = fun j => (x j : ℝ) := by
    rw [← hR]
    exact LinearMap.congr_fun hL (fun j => (x j : ℝ))
  simpa only [hx, norm_pi_int_cast] using Lc.le_opNorm (fun i => (T x i : ℝ))

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- Laurent coordinates of the actual rational valuation image grow at
most linearly in the height of any closed matrix realization. -/
def RationalValuationCoordinateHeightStatement : Prop :=
  ∀ hG : IsConnectedReductive G, IsClosedSubgroup ρ →
    ∃ C : ℝ, 0 < C ∧ ∀ g : rationalPoints G,
      ‖rationalValuationCoordinates G hG g‖ ≤ C * (1 + rationalHeight (F := F) ρ g)

open SplitCenterHeight in
/-- Read the valuation on a basis of actual rational characters, then use
the real linear retraction to control the image-lattice coordinates. -/
theorem rationalValuationCoordinateHeight :
    RationalValuationCoordinateHeightStatement ρ := by
  intro hG hρ
  let := (rationalCharacterLattice F G hG).1
  let := (rationalCharacterLattice F G hG).2
  let I := Module.Free.ChooseBasisIndex ℤ (rationalCharacters G)
  let : Fintype I := Fintype.ofFinite I
  let b : Module.Basis I ℤ (rationalCharacters G) := Module.Free.chooseBasis ℤ _
  let eval : Additive (rationalDiscreteValuationImage G) →+ (I → ℤ) :=
    { toFun := fun x j =>
        (show ↥(rationalCharacterValuationImage G) from x.toMul).val.toAdd (b j)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have heval : Function.Injective eval := by
    intro x y h
    change (show ↥(rationalCharacterValuationImage G) from x.toMul) = y.toMul
    apply Subtype.ext
    change (show ↥(rationalCharacterValuationImage G) from x.toMul).val.toAdd =
      (show ↥(rationalCharacterValuationImage G) from y.toMul).val.toAdd
    let fx := (show ↥(rationalCharacterValuationImage G) from x.toMul).val.toAdd
    let fy := (show ↥(rationalCharacterValuationImage G) from y.toMul).val.toAdd
    have hxy : fx.toIntLinearMap = fy.toIntLinearMap :=
      b.ext fun j => congrFun h j
    exact AddMonoidHom.ext fun χ => LinearMap.congr_fun hxy χ
  let e := rationalValuationLatticeEquiv G hG
  let T := (eval.comp e.symm.toAddMonoidHom).toIntLinearMap
  obtain ⟨D, hD, hnorm⟩ :=
    exists_norm_le_of_int_linear_injective T (heval.comp e.symm.injective)
  choose C hC hbound using fun j => exists_abs_valuation_le ρ hρ (b j)
  let B := ∑ j, C j
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => (hC j).le
  refine ⟨D * B + 1, by positivity, fun g => ?_⟩
  have hval (j : I) : T (rationalValuationCoordinates G hG g) j = valuation (b j) g := by
    change eval (e.symm (e (Additive.ofMul (rationalValuationImageProjection G g)))) j = _
    rw [e.symm_apply_apply]
    rfl
  have hheight := rationalHeight_nonneg ρ g
  have hT : ‖T (rationalValuationCoordinates G hG g)‖ ≤
      B * (1 + rationalHeight (F := F) ρ g) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (by linarith))).mpr
    intro j
    rw [hval, ← Int.norm_cast_real, Real.norm_eq_abs]
    exact (hbound j g).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ j)) (by linarith))
  calc
    _ ≤ D * ‖T (rationalValuationCoordinates G hG g)‖ := hnorm _
    _ ≤ D * (B * (1 + rationalHeight (F := F) ρ g)) := mul_le_mul_of_nonneg_left hT hD
    _ ≤ (D * B + 1) * (1 + rationalHeight (F := F) ρ g) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by linarith)

namespace RationalSemistandard

variable [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} (m : LeviModel p)

attribute [local instance] modelAffine modelTopology

/-- The literal Levi's torus coordinates use the valuation coordinates
of its representing scheme through the actual point homeomorphism. -/
theorem LeviModel.laurentExponent_eq_valuationCoordinates (x : levi p) :
    laurentExponent m.normCharacters m.unitaryCoordinates.toMulEquiv
      m.unitaryCoordinates_hasLaurent x =
    rationalValuationCoordinates m.scheme m.reductive (m.pointHomeomorph.symm x) := by
  refine laurentExponent_eq_of_forall _ _ _ fun z => ?_
  change ((((rationalCanonicalUnitaryUnramifiedCharacterCoordinates m.scheme m.reductive).symm
    z).val (m.pointHomeomorph.symm x) : ℂˣ) : ℂ) = _
  exact rationalUnitaryUnramifiedCharacter_apply m.scheme m.reductive z (m.pointHomeomorph.symm x)

/-- The Laurent height hypothesis in the actual semistandard Fourier
regularity theorem follows for the restriction of the ambient height. -/
theorem LeviModel.exists_laurentExponent_height_bound (hρ : IsClosedSubgroup ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : levi p,
      ‖laurentExponent m.normCharacters m.unitaryCoordinates.toMulEquiv
          m.unitaryCoordinates_hasLaurent x‖ ≤ C * (1 + rationalHeight (F := F) ρ x) := by
  let : IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom
  obtain ⟨C, hC, hb⟩ := rationalValuationCoordinateHeight (ρ.restrict m.inclusion) m.reductive
    (isClosedSubgroup_restrict_semistandardLevi ρ p m hρ)
  refine ⟨C, hC, fun x => ?_⟩
  rw [m.laurentExponent_eq_valuationCoordinates]
  have hx := hb (m.pointHomeomorph.symm x)
  rwa [rationalHeight_restrict_semistandardLevi ρ p m,
    ContinuousMulEquiv.apply_symm_apply] at hx

end RationalSemistandard

end Langlands.HarishChandraSchwartz
