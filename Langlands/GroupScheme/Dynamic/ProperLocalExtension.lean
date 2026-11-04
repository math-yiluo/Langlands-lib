import Langlands.GroupScheme.Dynamic.FieldPointBasicOpen
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Extending field points over valuation rings, and points of local schemes in opens

For a proper scheme `X` over a field `Ω`, every point of `X` over the fraction field `K'` of a
valuation ring `A` over `Ω` extends over `A`. Here `K'` is any fraction field model, not only
`FractionRing A`. Also, a point of a scheme over a local ring `A` whose closed point lands in an
open `C` lands in `C` entirely.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace Langlands.GroupScheme

namespace Corepresented

variable {Ω : Type u} [Field Ω]

/-- **Valuative criterion, existence part.** For a proper `X` over `Spec Ω`, a valuation ring
`A` over `Ω` and a field of fractions `K'` of `A`, every point of `X` over `K'` extends over
`A`. -/
theorem exists_extension_of_isProper (X : Over (Spec (CommRingCat.of Ω))) [IsProper X.hom]
    (A K' : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [Algebra Ω A] [Field K']
    [Algebra A K'] [IsFractionRing A K'] [Algebra Ω K'] [IsScalarTower Ω A K']
    (x : algOver Ω K' ⟶ X) :
    ∃ xA : algOver Ω A ⟶ X, algOverHom (IsScalarTower.toAlgHom Ω A K') ≫ xA = x := by
  have hVC : ValuativeCriterion.Existence X.hom := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) X.hom := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  let sq : ValuativeCommSq X.hom :=
    { R := A
      K := K'
      i₁ := x.left
      i₂ := (algOver Ω A).hom
      commSq := ⟨by
        change x.left ≫ X.hom =
          Spec.map (CommRingCat.ofHom (algebraMap A K')) ≫ (algOver Ω A).hom
        rw [Over.w x]
        exact (specMap_comp_specMap_algebraMap (IsScalarTower.toAlgHom Ω A K')).symm⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (hVC sq).exists_lift
  exact ⟨Over.homMk l hl₂, Over.OverMorphism.ext hl₁⟩

/-- A point over a local ring whose closed point lands in an open lands in it entirely. -/
theorem range_subset_of_residue (A : Type u) [CommRing A] [IsLocalRing A] [Algebra Ω A]
    {Y : Over (Spec (CommRingCat.of Ω))} (y : algOver Ω A ⟶ Y) {C : Set Y.left}
    (hC : IsOpen C)
    (h : Set.range (algOverHom (IsScalarTower.toAlgHom Ω A (ResidueField A)) ≫ y).left ⊆ C) :
    Set.range y.left ⊆ C := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨s⟩ : Nonempty (Spec (CommRingCat.of (ResidueField A))) := inferInstance
  have hs : Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A))) s =
      (closedPoint A : PrimeSpectrum A) := by
    rw [Spec.map_apply]
    have hbot : (s : PrimeSpectrum (ResidueField A)) = closedPoint (ResidueField A) :=
      PrimeSpectrum.ext (by
        have := s.isPrime
        rw [Ideal.eq_bot_of_prime s.asIdeal]
        exact (IsLocalRing.maximalIdeal_eq_bot (R := ResidueField A)).symm)
    change PrimeSpectrum.comap (algebraMap A (ResidueField A)) s = _
    rw [hbot]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
  have hmem : y.left (closedPoint A : PrimeSpectrum A) ∈ C := by
    rw [← hs]
    exact h ⟨s, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint (t : PrimeSpectrum A)).map
    y.left.continuous).mem_open hC hmem

end Corepresented

end Langlands.GroupScheme
