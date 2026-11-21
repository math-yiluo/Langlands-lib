import Langlands.Automorphic.GroupSchemeInfiniteTranslation
import Langlands.Global.AdelicEisensteinGrowthBound

/-! # Infinite right translation with conjugation of the compact subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.InfiniteAdelicGroupPoints
  Langlands.Global.RepresentationGrowth Langlands.GroupScheme Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

private def infiniteSliceRightTranslation (a : InfiniteAdelicGroupPoints F G) :
    Module.End ℂ (InfinitePlotSmoothFunctions F G) :=
  G.plotSmoothRightAction (CommAlgCat.of F (InfiniteAdeleRing F))
    (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom a

private theorem infiniteSliceRightTranslation_envelopingAction
    (a : InfiniteAdelicGroupPoints F G) (D : AdelicEnvelopingAlgebra F G hsmooth)
    (f : InfinitePlotSmoothFunctions F G) :
    infiniteSliceRightTranslation a (plotSmoothEnvelopingAction F G hsmooth hcalc D f) =
      plotSmoothEnvelopingAction F G hsmooth hcalc (adelicEnvelopingConjugation F G hsmooth a D)
        (infiniteSliceRightTranslation a f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  obtain ⟨p, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) D
  induction p using TensorAlgebra.induction generalizing f with
  | algebraMap z =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      LinearMap.smul_apply, Module.End.one_apply]
  | «ι» X =>
    change infiniteSliceRightTranslation a (plotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.ι ℂ X) f) =
      plotSmoothEnvelopingAction F G hsmooth hcalc
        (adelicEnvelopingConjugation F G hsmooth a (UniversalEnvelopingAlgebra.ι ℂ X))
        (infiniteSliceRightTranslation a f)
    induction X using TensorProduct.inductionOn with
    | tmul z X =>
      rw [adelicEnvelopingConjugation_ι_tmul]
      simp only [plotSmoothEnvelopingAction_generator, complexPlotSmoothLieAction_tmul,
        LinearMap.smul_apply, map_smul]
      apply congrArg (z • ·)
      apply Subtype.ext
      funext x
      exact groupDirectionalValue_rightTranslation 𝓘(ℝ, smoothModel F d) a X
        ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp f.property) x
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply, hX, hY]
  | mul p q hp hq =>
    simp only [map_mul, Module.End.mul_apply, hp, hq]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]

private def centerConjugationEquiv (a : InfiniteAdelicGroupPoints F G) :
    AdelicEnvelopingCenter F G hsmooth ≃ₐ[ℂ] AdelicEnvelopingCenter F G hsmooth where
  toFun := adelicCenterConjugation F G hsmooth a
  invFun := adelicCenterConjugation F G hsmooth a⁻¹
  left_inv z := Subtype.ext (by
    simp only [adelicCenterConjugation_val, ← adelicEnvelopingConjugationEquiv_apply,
      ← adelicEnvelopingConjugationEquiv_symm_apply F G hsmooth a,
      AlgEquiv.symm_apply_apply])
  right_inv z := Subtype.ext (adelicEnvelopingConjugation_apply_inv F G hsmooth a z.val)
  map_add' x y := Subtype.ext (map_add (adelicEnvelopingConjugation F G hsmooth a) x.val y.val)
  map_mul' x y := Subtype.ext (map_mul (adelicEnvelopingConjugation F G hsmooth a) x.val y.val)
  commutes' z := Subtype.ext ((adelicEnvelopingConjugation F G hsmooth a).commutes z)

omit [IsAffine G.X.left] in
private theorem HasModerateGrowthFunction.rightTranslate
    {N : ℕ} {rho : MatrixRepresentation G (Fin N)} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : HasModerateGrowthFunction F G rho φ) (a : AdelicGroupPoints F G) :
    HasModerateGrowthFunction F G rho (fun x => φ (x * a)) := by
  obtain ⟨r, _, h⟩ := RepresentationGrowth.HasModerateGrowthFunction.exists_compact_mul_le_height hφ
  obtain ⟨C, hC, hbound⟩ := h {a} isCompact_singleton
  have hbound' (x : AdelicGroupPoints F G) : ‖φ (x * a)‖ ≤ C * adelicHeightAtLeastOne rho x ^ r :=
    hbound x a (Set.mem_singleton a)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hm (x : AdelicGroupPoints F G) : adelicMatrix F G rho x = 1 := by
      apply Units.ext
      ext i j
      exact Fin.elim0 i
    let B := max 1 (AdelicMatrixHeight.height F 0 1)
    have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨C * B ^ r, mul_pos hC (Real.rpow_pos_of_pos hB _), 0, fun x => ?_⟩
    simpa only [Real.rpow_zero, mul_one, adelicHeightAtLeastOne, adelicHeight, hm, B] using hbound' x
  · let B : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
    have hB : 0 < B := pow_pos (Nat.cast_pos.mpr hN) _
    refine ⟨C * B ^ r, mul_pos hC (Real.rpow_pos_of_pos hB _), r, fun x => ?_⟩
    calc
      _ ≤ C * adelicHeightAtLeastOne rho x ^ r := hbound' x
      _ = _ := by
        rw [adelicHeightAtLeastOne_eq hN, adelicHeight_eq_scalar_mul_sourceNorm,
          Real.mul_rpow hB.le (adelicSourceNorm_pos F G rho hN x).le, mul_assoc]

/-- Right translation by an infinite adelic point conjugates the right compact
subgroup and preserves all other automorphy requirements. -/
theorem IsAutomorphicFunctionOn.infiniteRightTranslate
    {N : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {Γ : Subgroup (AdelicGroupPoints F G)} {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {φ : AdelicGroupPoints F G → ℂ} (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ)
    (a : InfiniteAdelicGroupPoints F G) :
    IsAutomorphicFunctionOn F G hsmooth hcalc Γ (Kinf.map (MulAut.conj a).toMonoidHom) rho
      (fun x => φ (x * ofInfinite F G a)) := by
  let A := ofInfinite F G a
  let f : AdelicGroupPoints F G → ℂ := fun x => φ (x * A)
  obtain ⟨hInv, hSmooth, hKfinite, hCenter, hGrowth⟩ := hφ
  let slice (b : FiniteAdelicGroupPoints F G) : InfinitePlotSmoothFunctions F G :=
    ⟨functionInfiniteSlice F G φ b, hSmooth.2.1 b⟩
  have hslice (b : FiniteAdelicGroupPoints F G) :
      functionInfiniteSlice F G f b = (infiniteSliceRightTranslation a (slice b)).val := by
    funext x
    change φ (pair F G x b * ofInfinite F G a) = φ (pair F G (x * a) b)
    rw [ofInfinite_eq_pair, pair_mul, mul_one]
  refine ⟨?_, ?_, ?_, ?_, hGrowth.rightTranslate A⟩
  · intro x hx y
    change φ ((x * y) * A) = φ (y * A)
    rw [mul_assoc, hInv x hx]
  · obtain ⟨L, hL, hfix⟩ := hSmooth.2.2
    refine ⟨hSmooth.1.comp (continuous_id.mul continuous_const),
      fun b => (hslice b).symm ▸ (infiniteSliceRightTranslation a (slice b)).2, L, hL, ?_⟩
    intro y hy x
    change φ ((x * ofFinite F G y) * A) = φ (x * A)
    have hComm : ofFinite F G y * A = A * ofFinite F G y := (factors_commute F G a y).eq.symm
    rw [mul_assoc, hComm, ← mul_assoc]
    exact hfix y hy (x * A)
  · let V := Submodule.span ℂ (Set.range fun k : Kinf =>
      fun x => φ (x * ofInfinite F G k.val))
    let T : (AdelicGroupPoints F G → ℂ) →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
      { toFun := fun h x => h (x * A)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let : FiniteDimensional ℂ V := hKfinite
    apply Submodule.finiteDimensional_of_le (S₂ := V.map T)
    apply Submodule.span_le.mpr
    intro h hh
    obtain ⟨k, rfl⟩ := hh
    obtain ⟨k₀, hk₀, hk⟩ := k.2
    refine ⟨_, Submodule.subset_span ⟨⟨k₀, hk₀⟩, rfl⟩, ?_⟩
    funext x
    change φ ((x * A) * ofInfinite F G k₀) = φ ((x * ofInfinite F G k.val) * A)
    have hkc : (k : InfiniteAdelicGroupPoints F G) = a * k₀ * a⁻¹ := hk.symm
    rw [hkc, map_mul, map_mul, map_inv]
    change φ ((x * ofInfinite F G a) * ofInfinite F G k₀) =
      φ ((x * (ofInfinite F G a * ofInfinite F G k₀ * (ofInfinite F G a)⁻¹)) * ofInfinite F G a)
    congr 1
    group
  · obtain ⟨I, hI, hAnn⟩ := hCenter
    let C := centerConjugationEquiv (hsmooth := hsmooth) a
    let I' := I.map C.toRingHom
    let : Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ I.restrictScalars ℂ) := hI
    let Q := (I.restrictScalars ℂ).mapQ (I'.restrictScalars ℂ) C.toLinearEquiv.toLinearMap
      (fun x hx => Ideal.mem_map_of_mem C.toRingHom (show x ∈ I from hx))
    have hI' : Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ I'.restrictScalars ℂ) := by
      apply Module.Finite.of_surjective Q
      intro y
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (I'.restrictScalars ℂ) y
      refine ⟨Submodule.Quotient.mk (C.symm z), ?_⟩
      change (Submodule.Quotient.mk (C (C.symm z)) : _ ⧸ I'.restrictScalars ℂ) =
        Submodule.Quotient.mk z
      rw [AlgEquiv.apply_symm_apply]
    refine ⟨I', hI', fun z hz b hb => ?_⟩
    obtain ⟨z₀, hz₀, rfl⟩ := (Ideal.mem_map_iff_of_surjective C.toRingHom C.surjective).mp hz
    have hs : (⟨functionInfiniteSlice F G f b, hb⟩ : InfinitePlotSmoothFunctions F G) =
        infiniteSliceRightTranslation a (slice b) := Subtype.ext (hslice b)
    rw [hs]
    change plotSmoothEnvelopingAction F G hsmooth hcalc
      (adelicEnvelopingConjugation F G hsmooth a z₀.val)
      (infiniteSliceRightTranslation a (slice b)) = 0
    rw [← infiniteSliceRightTranslation_envelopingAction hcalc]
    have hz : plotSmoothEnvelopingAction F G hsmooth hcalc z₀.val (slice b) = 0 :=
      hAnn z₀ hz₀ b (hSmooth.2.1 b)
    rw [hz, map_zero]

/-- Infinite right translation transports the original automorphy predicate
on a fixed left quotient to the conjugate infinite compact subgroup. -/
def AutomorphicInfiniteRightTranslationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (N d : ℕ) (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (Γ : Subgroup (AdelicGroupPoints F G)) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (φ : AdelicGroupPoints F G → ℂ) (a : InfiniteAdelicGroupPoints F G),
    IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ →
      IsAutomorphicFunctionOn F G hsmooth hcalc Γ (Kinf.map (MulAut.conj a).toMonoidHom) rho
        (fun x => φ (x * ofInfinite F G a))

theorem automorphicInfiniteRightTranslation : AutomorphicInfiniteRightTranslationStatement.{u} := by
  intro F _ _ G _ N d rho hsmooth hcalc Γ Kinf φ a hφ
  exact IsAutomorphicFunctionOn.infiniteRightTranslate hcalc hφ a

end Langlands.Automorphic.GroupSchemeFunctions
