import Langlands.Representation.Plancherel.RationalKernelUnitaryCoordinate
import Langlands.Representation.Plancherel.LaurentBlockPolynomialPresentation
import Langlands.Representation.Plancherel.ContinuedScalarNormBound
import Langlands.Representation.Plancherel.UnitCirclePoleRemoval
import Langlands.Representation.Plancherel.RationalUnitaryRegularValue

/-! # Unitary regularity of ambient-invariant fractions in rank at most one -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.ValuationKernelCoordinates

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance rankOneSourceTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X
local instance rankOneAmbientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable (hH : IsConnectedReductive H)

set_option hygiene false in
local notation "νH" => (fun ψ => (rationalNormCharacters H ψ).toMul)

set_option hygiene false in
local notation "KH" =>
  rationalUnramifiedFunctionField H (continuous_rationalValuationImageProjection H) hH

/-- One uniform norm bound for regular values on a dense subset of the
actual unitary character group. -/
def HasDenseUnitaryNormBound (f : KH) : Prop :=
  ∃ D : Set (unitaryUnramifiedCharacters νH), Dense D ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ chi ∈ D,
      RationalFunctionNormBoundedAt H (continuous_rationalValuationImageProjection H) hH
        f (unitaryToUnramified H chi) C

/-- Ambient invariance gives an actual product-coordinate fraction supported
on the block for the valuation kernel. -/
theorem exists_firstBlock_fraction_of_ambient_fixed {r n : ℕ}
    (e : Additive (rationalDiscreteValuationImage H) ≃ₗ[ℤ]
      (Fin r → ℤ) × (Fin n → ℤ))
    (i : H ⟶ G)
    (he : ∀ x : Additive (rationalDiscreteValuationImage H),
      (e x).2 = 0 ↔ rationalValuationImageMap i x.toMul = 1)
    (f : KH)
    (hf : ∀ eta : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul),
      rationalUnramifiedFunctionFieldTranslation H
        (continuous_rationalValuationImageProjection H) hH
        (rationalUnramifiedCharacterRestrict i eta) f = f) :
    ∃ p q : AddMonoidAlgebra ℂ (Fin r → ℤ), q ≠ 0 ∧
      (productFunctionFieldEquiv e hH).symm f =
        algebraMap _ (FractionRing (AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ))))
          (LaurentBlockInvariants.firstBlock (n := n) p) /
        algebraMap _ (FractionRing (AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ))))
          (LaurentBlockInvariants.firstBlock (n := n) q) :=
  LaurentBlockInvariants.exists_firstBlock_fraction_of_fixed
    (productRegularScaling e) (productRegularScaling_single e)
    (productFractionScaling e hH) (productFractionScaling_algebraMap e hH)
    ((productFunctionFieldEquiv e hH).symm f)
    (productFractionScaling_fixed_of_ambient_fixed e hH i he f hf)

/-- A reduced fraction in a single actual kernel coordinate is regular at
all unitary points once its regular values are bounded on a dense set. -/
theorem firstPolynomialFraction_regularAt_of_dense_normBound {n : ℕ}
    (e : Additive (rationalDiscreteValuationImage H) ≃ₗ[ℤ]
      (Fin 1 → ℤ) × (Fin n → ℤ))
    (f : KH) (p q : Polynomial ℂ) (hq : q ≠ 0) (hcop : IsCoprime p q)
    (hf : f = algebraMap (unramifiedRegularFunctions νH) KH (firstPolynomialMap e p) /
      algebraMap (unramifiedRegularFunctions νH) KH (firstPolynomialMap e q))
    (D : Set (unitaryUnramifiedCharacters νH)) (hD : Dense D)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ chi ∈ D,
      RationalFunctionNormBoundedAt H (continuous_rationalValuationImageProjection H) hH
        f ⟨chi.val, chi.property.1⟩ C)
    (chi : unitaryUnramifiedCharacters νH) :
    RationalFunctionRegularAt H (continuous_rationalValuationImageProjection H) hH
      f ⟨chi.val, chi.property.1⟩ := by
  have hCircle := firstPolynomialFraction_circle_bound_of_dense e D hD p q C hC
    (fun w hw hden => by
      obtain ⟨m, d, hd, hfd, hb⟩ := hbound w hw
      rw [rationalFunction_value_eq H (continuous_rationalValuationImageProjection H) hH
        hden hd hf hfd]
      exact hb)
  exact regularAt_of_firstPolynomialFraction e hH p q f hf chi
    (UnitCirclePoleRemoval.denominator_eval_ne_zero_of_coprime_div_bound
      p q hq hcop ∅ Set.finite_empty C (fun z _ => hCircle z) (firstUnitaryCoordinate e chi))

/-- An ambient-invariant fraction with a dense unitary norm bound is
regular on the entire unitary group when the valuation kernel has an
adapted product chart with at most one kernel coordinate. -/
theorem unitaryRegular_of_ambient_fixed_of_dense_normBound {r n : ℕ}
    (e : Additive (rationalDiscreteValuationImage H) ≃ₗ[ℤ]
      (Fin r → ℤ) × (Fin n → ℤ))
    (hr : r ≤ 1)
    (i : H ⟶ G)
    (he : ∀ x : Additive (rationalDiscreteValuationImage H),
      (e x).2 = 0 ↔ rationalValuationImageMap i x.toMul = 1)
    (f : KH)
    (hf : ∀ eta : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul),
      rationalUnramifiedFunctionFieldTranslation H
        (continuous_rationalValuationImageProjection H) hH
        (rationalUnramifiedCharacterRestrict i eta) f = f)
    (hb : HasDenseUnitaryNormBound hH f) :
    RationalFunctionUnitaryRegular H hH f := by
  have hr' : r = 0 ∨ r = 1 := by omega
  rcases hr' with rfl | rfl
  · obtain ⟨p, q, -, hpq⟩ := exists_firstBlock_fraction_of_ambient_fixed hH e i he f hf
    obtain ⟨c, hc⟩ := LaurentBlockInvariants.exists_constant_of_firstBlock_fraction
      p q ((productFunctionFieldEquiv e hH).symm f) hpq
    have hfc : f = algebraMap (unramifiedRegularFunctions νH) KH
        (algebraMap ℂ (unramifiedRegularFunctions νH) c) := by
      have h := congrArg (productFunctionFieldEquiv e hH) hc
      simpa only [RingEquiv.apply_symm_apply, productFunctionFieldEquiv,
        IsFractionRing.ringEquivOfRingEquiv_algebraMap, AlgEquiv.coe_ringEquiv,
        AlgEquiv.commutes] using h
    rw [hfc]
    exact rationalFunctionUnitaryRegular_algebraMap H hH _
  · obtain ⟨p, q, -, hpq⟩ := exists_firstBlock_fraction_of_ambient_fixed hH e i he f hf
    obtain ⟨P, Q, hQ, hcop, hPQ⟩ :=
      LaurentBlockInvariants.exists_coprime_firstPolynomial_fraction
        p q ((productFunctionFieldEquiv e hH).symm f) hpq
    have hmap : (productLaurentAlgebraEquiv e).toAlgHom.comp
        (LaurentBlockInvariants.firstPolynomialMap (n := n)) = firstPolynomialMap e := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        LaurentBlockInvariants.firstPolynomialMap, firstPolynomialMap, Polynomial.aeval_X]
      rfl
    have hpol (p : Polynomial ℂ) :
        productLaurentAlgebraEquiv e (LaurentBlockInvariants.firstPolynomialMap (n := n) p) =
          firstPolynomialMap e p :=
      DFunLike.congr_fun hmap p
    have hfpq : f = algebraMap (unramifiedRegularFunctions νH) KH (firstPolynomialMap e P) /
        algebraMap (unramifiedRegularFunctions νH) KH (firstPolynomialMap e Q) := by
      have h := congrArg (productFunctionFieldEquiv e hH) hPQ
      simpa only [RingEquiv.apply_symm_apply, map_div₀, productFunctionFieldEquiv,
        IsFractionRing.ringEquivOfRingEquiv_algebraMap, AlgEquiv.coe_ringEquiv, hpol] using h
    obtain ⟨D, hD, C, hC, hbD⟩ := hb
    exact firstPolynomialFraction_regularAt_of_dense_normBound
      hH e f P Q hQ hcop hfpq D hD C hC hbD

end Langlands.Plancherel.ValuationKernelCoordinates
