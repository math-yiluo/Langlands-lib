import Langlands.Global.AdelicEisensteinGrowthBound
import Langlands.Global.AdelicParabolicProjectiveHeight
import Langlands.Global.ProjectiveSectionChart
import Langlands.Global.RationalMatrixHeightComparison
import Langlands.GroupScheme.ParabolicProjectiveSections
import Langlands.GroupScheme.FlagCoreTorus
import Langlands.GroupScheme.Rational.MatrixEntryBoundedness

/-! # Polynomially bounded representatives of rational parabolic cosets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints AdelicMatrixHeight

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F : Type u} [Field F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {p : P ⟶ G} {N : ℕ} (rho : MatrixRepresentation G (Fin N))

/-- The regular function of a matrix entry or an inverse entry in a representation. -/
def matrixAndInverseEntryFunction : MatrixAndInverseIndex N → AffineCoordinateRing F G.X
  | .inl (i, j) => rho.hom.hom.left.appTop
      (GeneralLinear.entrySection (Fin N) (CommRingCat.of F) i j)
  | .inr (i, j) => rho.hom.hom.left.appTop
      (GeneralLinear.inverseEntrySection (Fin N) (CommRingCat.of F) i j)

theorem matrixAndInverseEntryFunction_eval (x : RationalPoint F G.X)
    (a : MatrixAndInverseIndex N) :
    rationalPointAlgebraHom F G.X x (matrixAndInverseEntryFunction rho a) =
      matrixAndInverseEntry (rho.rationalMatrix x) a := by
  rcases a with ⟨i, j⟩ | ⟨i, j⟩
  · rw [matrixAndInverseEntry, matrixAndInverseEntryFunction, rationalPointAlgebraHom_apply_appTop,
      rho.rationalMatrix_apply_apply x i j, Over.comp_left, Scheme.Hom.comp_appTop]
    rfl
  · rw [matrixAndInverseEntry, matrixAndInverseEntryFunction, rationalPointAlgebraHom_apply_appTop,
      rho.rationalMatrix_inv_apply_apply x i j, Over.comp_left, Scheme.Hom.comp_appTop]
    rfl

variable [NumberField F] {m : ℕ}
  (σ : MatrixRepresentation G (Fin (m + 1))) (j : Fin (m + 1))

private theorem exists_bounded_lifts (D : ParabolicProjectiveSections p σ j) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ x : RationalPoint F G.X,
      ∃ y : RationalPoint F G.X, y ≫ D.projection = x ≫ D.projection ∧
        max 1 (AdelicMatrixHeight.height F N (AdelicGL.rational F N (rho.rationalMatrix y))) ≤
          C * Height.mulHeight ((σ.rationalMatrix x).val *ᵥ Pi.single j 1) ^ d := by
  classical
  let e := D.polynomialEmbedding
  let : IsClosedImmersion e := D.isClosedImmersion_polynomialEmbedding
  let : IsProper D.quotient.hom := D.proper
  let : IsNoetherian D.quotient.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian D.quotient.hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace D.quotient.hom }
  let Chart := ProjectiveSectionChart e D.projection
  obtain ⟨t, hcover⟩ := ProjectiveSectionChart.exists_finite_cover
    (e := e) (q := D.projection) D.polynomialEmbedding_toSpec D.localSections
  let I (S : Chart) := {x : RationalPoint F G.X //
    (x ≫ D.projection).left (IsLocalRing.closedPoint F) ∈ S.inclusion.left.opensRange}
  let y (S : Chart) (x : I S) : RationalPoint F G.X :=
    S.pointLift (x.val ≫ D.projection) x.property ≫ S.lift
  let a (x : RationalPoint F G.X) : Fin (m + 1) → F :=
    (σ.rationalMatrix x).val *ᵥ Pi.single j 1
  have hbound (S : Chart) :
      ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ x : I S,
        max 1 (AdelicMatrixHeight.height F N
            (AdelicGL.rational F N (rho.rationalMatrix (y S x)))) ≤
          C * Height.mulHeight (a x.val) ^ d := by
    apply exists_rational_height_powerBound F (fun x : I S => rho.rationalMatrix (y S x))
      (fun x => Height.mulHeight (a x.val)) (fun x => Height.one_le_mulHeight (a x.val))
    intro b
    have h := S.regularFunction_mem_polynomialHeightBounded D.polynomialEmbedding_toSpec
      (fun x : I S => x.val ≫ D.projection) (fun x => x.property)
      (fun x => a x.val) (fun x => D.hasCoordinates x.val)
      (matrixAndInverseEntryFunction rho b)
    simpa only [matrixAndInverseEntryFunction_eval, y] using h
  choose C hC d hd using hbound
  let C₀ := 1 + ∑ S ∈ t, C S
  let d₀ := t.sup d
  have hCsum : 0 ≤ ∑ S ∈ t, C S := Finset.sum_nonneg fun S _ => (hC S).le
  refine ⟨C₀, add_pos_of_pos_of_nonneg zero_lt_one hCsum, d₀, fun x => ?_⟩
  obtain ⟨S, hS, hx⟩ := hcover (x ≫ D.projection)
  let xi : I S := ⟨x, hx⟩
  refine ⟨y S xi, ?_, ?_⟩
  · change (S.pointLift (x ≫ D.projection) hx ≫ S.lift) ≫ D.projection = x ≫ D.projection
    rw [Category.assoc, S.lift_comp, S.pointLift_comp]
  have hCS : C S ≤ C₀ :=
    (Finset.single_le_sum (fun S _ => (hC S).le) hS).trans (le_add_of_nonneg_left zero_le_one)
  have hdS : d S ≤ d₀ := Finset.le_sup hS
  have hH : 1 ≤ Height.mulHeight (a x) := Height.one_le_mulHeight _
  exact (hd S xi).trans (mul_le_mul hCS (pow_le_pow_right₀ hH hdS)
    (pow_nonneg (zero_le_one.trans hH) _) (by linarith [hCsum]))

/-- Every rational parabolic coset has a representative of adelic matrix
height bounded by a fixed power of its prescribed Chevalley projective height. -/
theorem exists_polynomial_rationalCoset_representatives
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p)
    (hstab : σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j) :
    ∃ C d : ℝ, 0 < C ∧ 0 ≤ d ∧ ∀ c : ParabolicRationalCosets F p,
      ∃ x : RationalGroupPoints F G, Quotient.mk _ ⟨rational F G x, ⟨x, rfl⟩⟩ = c ∧
        adelicHeightAtLeastOne rho (rational F G x) ≤
          C * (parabolicRationalProjectiveEmbedding σ j hstab c).mulHeight ^ d := by
  classical
  let D := parabolicProjectiveSections p σ j hG hp hstab
  obtain ⟨C, hC, d, hd⟩ := exists_bounded_lifts rho σ j D
  refine ⟨C, (d : ℝ), hC, Nat.cast_nonneg d, ?_⟩
  intro c
  induction c using Quotient.inductionOn with
  | _ z =>
    obtain ⟨z, hz⟩ := z
    obtain ⟨g, rfl⟩ := hz
    let E := FlagCore.baseAffineTestIso (R := CommRingCat.of F)
    let x : RationalPoint F G.X := E.hom ≫ g⁻¹
    obtain ⟨y, hy, hheight⟩ := hd x
    let y₀ : RationalGroupPoints F G := E.inv ≫ y
    let g₀ := y₀⁻¹
    refine ⟨g₀, ?_, ?_⟩
    · have hmem := (D.fibers _ x y).mp hy.symm
      obtain ⟨b, hb⟩ := hmem
      change RationalPoint F P.X at b
      change b ≫ p.hom.hom = x⁻¹ * y at hb
      have hrel : (E.inv ≫ b) ≫ p.hom.hom = g * y₀ := by
        rw [Category.assoc, hb, MonObj.comp_mul, GrpObj.comp_inv]
        simp only [x, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, inv_inv, y₀]
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      change rational F G g * (rational F G g₀)⁻¹ ∈
        (rationalSubgroup F P).map (map F P G p).toMonoidHom
      let b₀ : RationalGroupPoints F P := E.inv ≫ b
      refine ⟨rational F P b₀, ⟨b₀, rfl⟩, ?_⟩
      have hnat : rational F G (b₀ ≫ p.hom.hom) = map F P G p (rational F P b₀) :=
        DFunLike.congr_fun (rational_naturality F P p) b₀
      change map F P G p (rational F P b₀) = _
      rw [← hnat, show b₀ ≫ p.hom.hom = g * y₀ from hrel, map_mul]
      simp only [g₀, map_inv, inv_inv]
    · have hρ : rho.rationalMatrix y = rationalMatrix F G rho y₀ := by
        have he : (FlagCore.baseAffineTestIso (R := CommRingCat.of F)).hom ≫ y₀ = y := by
          simp only [y₀, ← Category.assoc, Iso.hom_inv_id, Category.id_comp, E]
        rw [← he, FlagCore.rationalMatrix_baseAffineTestIso]
        rfl
      have hσ : σ.rationalMatrix x = rationalMatrix F G σ g⁻¹ :=
        FlagCore.rationalMatrix_baseAffineTestIso σ g⁻¹
      rw [adelicHeightAtLeastOne, show rational F G g₀ = (rational F G y₀)⁻¹ from map_inv _ _,
        adelicHeight_inv, adelicHeight, adelicMatrix_rational, ← hρ]
      rw [parabolicRationalProjectiveEmbedding_mk, rationalOrbitPoint,
        Projectivization.mulHeight_mk, ← hσ, Real.rpow_natCast]
      exact hheight

end Langlands.Global.RepresentationGrowth
