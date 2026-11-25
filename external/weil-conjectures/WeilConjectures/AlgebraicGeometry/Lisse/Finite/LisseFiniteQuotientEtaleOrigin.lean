/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOriginCore
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOriginTransport

/-! # Single finite quotient origins and their conditional constant-model transport

## References

* Stacks Project, Tags 09AL and 09B1, and coefficient transport in Tag 09C6
* Stacks Project, Tag 09AL (compare-constructible-derived), Tag 09B1 (compare-derived), and Tag
  09C6, construction of an individual etale origin
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- One finite quotient descended to an etale chart. No point, normalization arrow,
or choice of a constant model is included. Transport accepts any supplied model. -/
structure LisseFiniteQuotientEtaleOrigin
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (V : Y.Etale) where
  level : DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
  lisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor _ q).obj level)
  vanishing : ∀ q : ℤ,
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj level)
  refinementLisse : ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj V) (q : ℤ),
    IsRelativelyFiniteLisseModule (W.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (W.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((adicTowerPullback (W.hom ≫ g)
              ((pbcAdicRings X d).obj (op n))).obj K)))
  transport : ∀ (Z : V.left.Etale)
    (E : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))),
    Nonempty ((AlgebraicGeometry.Etale.upperStar _ Z.hom).mapDerivedCategory.obj level ≅
      (constantSheaf Z.left.smallEtaleTopology _).mapDerivedCategory.obj E) →
    ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj (Etale.mk (Z.hom ≫ V.hom))),
      Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
        (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj K)

/-- Descend a single bounded relatively finite lisse quotient complex, retaining
vanishing and transport on all further charts. This has no tower or normalization input. -/
theorem lisse_finite_quotient_etale_origin
    (X Y : Scheme.{u}) [IsNoetherian X] (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hlisse : ∀ q : ℤ,
      IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj K))))
    (V : Y.Etale) :
    Nonempty (LisseFiniteQuotientEtaleOrigin X Y g d n K V) := by
  obtain ⟨C⟩ := lisse_finite_quotient_etale_origin_core X Y g d n K hbounded hlisse V
  refine ⟨{ level := C.level
            lisse := C.lisse
            vanishing := C.vanishing
            refinementLisse := C.refinementLisse
            transport := ?_ }⟩
  intro Z E hE W w
  exact lisse_finite_quotient_etale_origin_transport C Z E hE W w

end AlgebraicGeometry.Scheme
