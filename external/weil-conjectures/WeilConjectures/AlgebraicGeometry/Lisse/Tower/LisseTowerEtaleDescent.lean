/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteLevelEtaleDescent
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleNormalizationDescent
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleUniversalNormalization

/-! # Descent of finite levels and their normalization arrows

## References

* Stacks Tags 099Z and 09B1 (bounded-below classical comparison), 099Y (finite locally constant
  descent), 09BV (Isom torsors), and 06YY (derived base change)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization
/-- Separately locally algebraic finite levels descend, together with the actual
normalization arrows. The constant comparison is natural for every algebraic source
arrow; this theorem has no supplied source normalization, no reduction on Isom sheaves,
and no evaluation of sheaf sections. -/
theorem lisse_tower_etale_descent
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt)
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u + 1}
      (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (hbounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (K n)))
    (hfinite : ∀ (n : ℕ) (q : ℤ), Module.Finite
      (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) q).obj (K n)))
    (hmodels : ∀ n : ℕ, ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj (K n) ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj (M.level n))) :
    Nonempty (LisseTowerEtaleDescent X Y g d M U K) := by
  classical
  have h (n : ℕ) := lisse_finite_level_etale_descent X Y g d U n (M.level n) (K n)
    (hbounded n) (hfinite n) (hmodels n)
  choose D hb hl hs he using h
  have e (n : ℕ) := (he n).some
  obtain ⟨N⟩ := lisse_tower_etale_normalization_descent X Y g d M U D hb e
  exact ⟨{
    D := D
    boundedD := hb
    lisseD := hl
    stalk := hs
    delta := N.delta
    local_delta_universal := fun n ↦ (N.local_delta n).universal
    local_constant_universal := N.local_constant_universal
    restriction_square := by
      intro n E E' k V Z f e e' he
      exact CategoryTheory.normalizationSquareTransport
        (Etale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))
          f.left).mapDerivedCategory
        (Etale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))
          f.left).mapDerivedCategory
        (normalizationRestrict Z.left.smallEtaleTopology (lisseTowerEtaleQuotient d n))
        (normalizationRestrict V.left.smallEtaleTopology (lisseTowerEtaleQuotient d n))
        (etaleNormalizationCoefficients f.left (lisseTowerEtaleQuotient d n))
        ((localIsomorphismRestrictionComp U.left (lisseTowerEtaleRing d (n + 1)) f).app
          ((normalizationConstant U.left.smallEtaleTopology).obj E)).symm
        ((localIsomorphismRestrictionComp U.left (lisseTowerEtaleRing d (n + 1)) f).app
          (D (n + 1))).symm
        ((localIsomorphismRestrictionComp U.left (lisseTowerEtaleRing d n) f).app
          ((normalizationConstant U.left.smallEtaleTopology).obj E')).symm
        ((localIsomorphismRestrictionComp U.left (lisseTowerEtaleRing d n) f).app (D n)).symm
        (etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
          (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
            k) Z)
        (etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n) (N.delta n) Z)
        (etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
          (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
            k) V)
        (etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n) (N.delta n) V)
        (N.constant_coherence n E E' k f) ((N.local_delta n).coherence f) e e' he
    realization := N.realization
    model := N.model
    actual := N.actual
    scalar := N.scalar
    actual_normalized := N.actual_normalized
    model_normalized := N.model_normalized }⟩

end AlgebraicGeometry.Scheme
