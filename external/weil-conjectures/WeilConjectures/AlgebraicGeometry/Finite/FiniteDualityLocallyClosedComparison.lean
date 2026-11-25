/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedComparisonCoordinates
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleLocallyClosedExtensionComparison
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedComparisonCoordinates
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion

/-!
# Locally closed exceptional comparison with its adjunction normalization

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-weil-finite-duality-site-comparison.proof.md, second paragraph
(blueprint: lem-weil-finite-duality-locally-closed-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- All clauses of locally closed exceptional comparison, on exactly bounded
constructible targets and bounded-below etale-origin tests. The natural transformations
are fixed by the counit and comparison-unit equations. The relative Hom equation is
required for every witness of etale origin and every normalized comparison-class datum.
Source: blueprint locally closed exceptional comparison, Steps 1--12
(blueprint: lem-weil-finite-duality-locally-closed-comparison). -/
structure LocallyClosedExceptionalComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsNoetherian T] [QuasiCompact (c ≫ v)] where
  adjoints : LocallyClosedComparisonAdjoints A c
  bounded (M : Etale.BoundedConstructibleDerivedCategory A T) :
    _root_.DerivedCategory.TStructure.t.plus ((adjoints.etaleRight v).obj M.obj)
  gamma :
    (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙ adjoints.etaleRight v ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ≅
      (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        adjoints.proetaleRight v
  counit (M : Etale.BoundedConstructibleDerivedCategory A T) :
    (locallyClosedExtensionComparison A c v).hom.app
        ⟨(adjoints.etaleRight v).obj M.obj, bounded M⟩ ≫
      (locallyClosedProEtaleExtension A c v).map (gamma.hom.app M) ≫
      (adjoints.proetalePasted v).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
        ((adjoints.etalePasted v).counit.app M.obj)
  transport :
    (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        adjoints.proetaleRight v ≅
      (Etale.DerivedCategory.isBoundedConstructible A T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        sfFiniteExceptionalAt A (locallyClosedImageCompactification (c ≫ v))
  unit_normalization (M : Etale.BoundedConstructibleDerivedCategory A T) :
    gamma.hom.app M ≫ transport.hom.app M =
      (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map
        ((locallyClosedEtaleRightIso v adjoints).hom.app M.obj ≫
          (locallyClosedEtaleExceptional A (c ≫ v)).map
            ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M.obj))
  relative_hom
      (B : FixedComparisonClassAdjunction A (c ≫ v)
        (locallyClosedImageCompactification (c ≫ v))
        (locallyClosedEtaleExceptional A (c ≫ v))
        (Adjunction.ofIsLeftAdjoint _)
        (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S)
        _root_.DerivedCategory.TStructure.t.plus)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
      (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S K)
      (M : Etale.BoundedConstructibleDerivedCategory A T)
      (hM : _root_.DerivedCategory.TStructure.t.plus
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj))
      (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (w : (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj L.obj ≅ K)
      (h : (locallyClosedProEtaleExtension A c v).obj K ⟶
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) :
    ((adjoints.proetalePasted v).homEquiv _ _) h ≫ transport.hom.app M =
      B.homEquiv (locallyClosedImageCompactification (c ≫ v)) K hK
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) hM
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
            (locallyClosedImageCompactification (c ≫ v))).map w.inv ≫
          (fixedCompactSupportComparisonIso A
            (locallyClosedImageCompactification (c ≫ v))).hom.app L ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
            ((locallyClosedEtaleSupportIso A c v).inv.app L.obj) ≫
          (locallyClosedExtensionComparison A c v).hom.app L ≫
          (locallyClosedProEtaleExtension A c v).map w.hom ≫ h)

private theorem normalizedComparison_unique
    {C₁ C₂ C₃ C₄ B : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category B]
    (ι : B ⥤ C₁) (CS : C₂ ⥤ C₄) (CT : C₁ ⥤ C₃) (U : C₃ ⥤ C₁)
    (η : 𝟭 C₁ ⟶ CT ⋙ U)
    (J J' X X' : C₁ ⥤ C₂) (P P' : C₃ ⥤ C₄) (hX : X = X')
    (r : J ≅ X) (r' : J' ≅ X')
    (γ : ι ⋙ J ⋙ CS ≅ ι ⋙ CT ⋙ P)
    (γ' : ι ⋙ J' ⋙ CS ≅ ι ⋙ CT ⋙ P')
    (θ : ι ⋙ CT ⋙ P ≅ ι ⋙ CT ⋙ U ⋙ X ⋙ CS)
    (θ' : ι ⋙ CT ⋙ P' ≅ ι ⋙ CT ⋙ U ⋙ X' ⋙ CS)
    (h : ∀ M, γ.hom.app M ≫ θ.hom.app M =
      CS.map (r.hom.app (ι.obj M) ≫ X.map (η.app (ι.obj M))))
    (h' : ∀ M, γ'.hom.app M ≫ θ'.hom.app M =
      CS.map (r'.hom.app (ι.obj M) ≫ X'.map (η.app (ι.obj M)))) :
    ∃! e : (J ≅ J') × (ι ⋙ CT ⋙ P ≅ ι ⋙ CT ⋙ P'),
      HEq (e.1 ≪≫ r') r ∧ HEq (e.2 ≪≫ θ') θ ∧
        ∀ M, CS.map (e.1.hom.app (ι.obj M)) ≫ γ'.hom.app M =
          γ.hom.app M ≫ e.2.hom.app M := by
  subst X'
  -- Both comparisons factor through the common normalized values.
  refine ⟨(r ≪≫ r'.symm, θ ≪≫ θ'.symm), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp
    · simp
    · intro M
      -- The two unit equations reduce the gamma square to inverse cancellation.
      apply (cancel_mono (θ'.hom.app M)).1
      simp only [Category.assoc, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Iso.inv_hom_id_app, Category.comp_id]
      rw [h', h]
      rw [← CS.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  · intro e he
    apply Prod.ext
    · apply Iso.ext
      apply (cancel_mono r'.hom).1
      simpa using congrArg Iso.hom (eq_of_heq he.1)
    · apply Iso.ext
      apply (cancel_mono θ'.hom).1
      simpa using congrArg Iso.hom (eq_of_heq he.2.1)

end AlgebraicGeometry.ProEtale
