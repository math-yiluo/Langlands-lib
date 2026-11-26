import Langlands.Global.AdelicCuspidalProductVanishing
import Langlands.Global.AdelicInducingConstantTermCovariance
import Langlands.Global.AdelicEisensteinParabolicRangeTransport

/-! # Moderate growth of nested standard constant terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
open AdelicSubgroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (fam : StandardParabolicFamily F G)

local notation "Index" => StandardIndex F G fam.i fam.ν
local notation "A" => AdelicGroupPoints F G
local notation "rad(" J ")" => SubgroupFunctor.range (fam.iU J ≫ fam.p J)
local notation "Γ(" J ")" => parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)
local notation "μ(" J ")" => normalizedRationalQuotientHaarMeasure F G (rad(J))

/-- The rational points of every nested parabolic fix a function on the larger
parabolic quotient. -/
theorem isLeftInvariantUnder_rationalImage_of_le {Q P : Index} (hQP : Q ≤ P)
    {f : A → ℂ} (hf : IsLeftInvariantUnder F G (Γ(P)) f) :
    IsLeftInvariantUnder F G (rationalImage F (fam.p Q)) f := by
  have hle := rationalImage_le_of_range_le (fam.p Q) (fam.p P)
    ((fam.le_iff_range_le Q P).mp hQP)
  exact fun x hx => hf x (rationalImage_le_parabolicQuotientSubgroup _ _ _
    (fam.isCompatible P).levi (fam.isUnipotentRadical P) (hle hx))

/-- The probability average defining a nested constant term preserves a
polynomial bound in the matrix height. -/
theorem hasHeightGrowth_constantTerm {N : ℕ} {rho : MatrixRepresentation G (Fin N)}
    (hN : 0 < N) (Q : Index) {f : A → ℂ}
    (hf : HasHeightGrowth rho f)
    (hInv : IsLeftInvariantUnder F G (rationalImage F (fam.p Q)) f) :
    HasHeightGrowth rho (fam.constantTerm Q f) := by
  let j := fam.iU Q ≫ fam.p Q
  let V := adelicPoints F G (rad(Q))
  let Δ := AdelicSubgroupPoints.rationalSubgroup F G (rad(Q))
  let : IsClosed (V : Set A) := isClosed_adelicPoints_range F G j
  let : CompactSpace (RationalQuotient F G (rad(Q))) := fam.compactSpace_radicalRationalQuotient Q
  let : IsProbabilityMeasure (μ(Q)) := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G (rad(Q))
  let H := adelicHeight F G rho
  have hH (x : A) : 0 ≤ H x := zero_le_one.trans (one_le_adelicHeight F G rho hN x)
  obtain ⟨C, r, hC, hr, hf⟩ := hf
  obtain ⟨B, hB⟩ := exists_le_of_compactSpace_leftCosetSpace Δ (fun n : V => H n.val)
    ((continuous_adelicHeight F G rho hN).comp continuous_subtype_val)
  have hB0 : 0 ≤ B := by
    obtain ⟨δ, _, hd⟩ := hB 1
    exact (hH (δ * (1 : V)).val).trans hd
  refine ⟨C * B ^ r, r, mul_nonneg hC (Real.rpow_nonneg hB0 _), hr, fun g => ?_⟩
  change ‖∫ q : RationalQuotient F G (rad(Q)), f ((Quotient.out q : V).val * g) ∂μ(Q)‖ ≤
    C * B ^ r * H g ^ r
  refine (norm_integral_le_of_norm_le_const (C := C * B ^ r * H g ^ r)
    (Filter.Eventually.of_forall fun q => ?_)).trans_eq (by simp)
  let v : V := Quotient.out q
  obtain ⟨δ, hδ, hδB⟩ := hB v
  let w : V := δ * v
  have hδQ : δ.val ∈ rationalImage F (fam.p Q) :=
    rationalImage_comp_le _ _ ((mem_rationalSubgroup_range_iff j δ).mp hδ)
  have heq : f (w.val * g) = f (v.val * g) := by
    change f ((δ.val * v.val) * g) = f (v.val * g)
    rw [mul_assoc, hInv _ hδQ]
  change ‖f (v.val * g)‖ ≤ _
  rw [← heq]
  have hw : H (w.val * g) ≤ B * H g :=
    (adelicHeight_mul_le F G rho hN _ _).trans (mul_le_mul_of_nonneg_right hδB (hH g))
  calc
    ‖f (w.val * g)‖ ≤ C * H (w.val * g) ^ r := hf _
    _ ≤ C * (B * H g) ^ r := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hH _) hw hr) hC
    _ = C * B ^ r * H g ^ r := by rw [Real.mul_rpow hB0 (hH g), mul_assoc]

/-- A nested constant term is continuous, has moderate growth and satisfies
both invariances of its parabolic quotient. -/
def AdelicParabolicConstantTermGrowthStatement : Prop :=
  ∀ {N : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N →
    ∀ {Q P : Index}, Q ≤ P → ∀ {f : A → ℂ}, fam.IsModerateContinuousOnParabolic rho P f →
      fam.IsModerateContinuousOnParabolic rho Q (fam.constantTerm Q f)

theorem adelicParabolicConstantTermGrowth : fam.AdelicParabolicConstantTermGrowthStatement := by
  intro N rho hN Q P hQP f hf
  have hInv := fam.isLeftInvariantUnder_rationalImage_of_le hQP hf.1
  obtain ⟨hCont, hRat, hRad⟩ := inducingConstantTermCovariance (fam.p Q) (fam.iU Q)
    (fam.isUnipotentRadical Q) f hf.2.1 hInv
  refine ⟨IsParabolicGeneratorInvariant.isLeftInvariantUnder fam ⟨?_, ?_⟩, hCont, ?_⟩
  · intro x g
    exact hRad x.val x.2 g
  · intro m g
    exact hRat _ (rationalImage_comp_le (fam.l Q) (fam.p Q) ⟨m, rfl⟩) g
  · exact (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mpr
      (fam.hasHeightGrowth_constantTerm hN Q
        ((hasModerateGrowthFunction_iff_hasHeightGrowth hN f).mp hf.2.2) hInv)

end Langlands.Global.StandardParabolicFamily
