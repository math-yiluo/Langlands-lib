/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCechResolutionDoubleComplex
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex

/-! # Augmentation normalization for additive étale Čech coordinates

Source: Stacks Project, Tags 03P2 and 01FD, the augmented double-complex diagram.
(blueprint: def-pbc-etale-additive-cech-normalization)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual inclusion of open subschemes in the small étale site.
Source: Stacks Project, Tag 03P2, the affine open covering.
(blueprint: def-pbc-etale-additive-cech-normalization) -/
noncomputable def additiveCechOpenInclusion (X : Scheme.{u}) : X.Opens ⥤ X.Etale :=
  MorphismProperty.Comma.lift X.restrictFunctor
    (fun W ↦ (inferInstance : Etale W.ι)) (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- The global-sections complex of an injective resolution.
Source: Stacks Project, Tag 01FD, the left augmentation.
(blueprint: def-pbc-etale-additive-cech-normalization) -/
noncomputable abbrev additiveCechGlobal {X : Scheme.{u}}
    (I : InjectiveResolution X.etaleAdditiveSheaf) :=
  ((Etale.etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex

/-- The total complex used for normalization, with Čech degree first.
Source: Stacks Project, Tags 03P2 and 01FD.
(blueprint: def-pbc-etale-additive-cech-normalization) -/
noncomputable abbrev additiveCechTotal {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (I : InjectiveResolution X.etaleAdditiveSheaf) :=
  (etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).total (.up ℕ)

/-- The degree-n global-section augmentation, obtained by restriction to each open.
Source: Stacks Project, Tag 01FD, augmentation alpha.
(blueprint: def-pbc-etale-additive-cech-normalization) -/
noncomputable def additiveCechAlpha {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :
    (additiveCechGlobal I).X n ⟶ (additiveCechTotal U I).X n :=
  Pi.lift (fun y : Fin 1 → ι ↦ (I.cocomplex.X n).obj.map
    (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ U (y l)).ι
      (Category.comp_id _) :
      (additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)) ⟶
        Scheme.Etale.mk (𝟙 X)).op) ≫
    (etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).ιTotal
      (.up ℕ) 0 n n (by simp)

/-- The coefficient augmentation on a cochain: lower module coordinates are
lifted, identified with functions on the open subscheme, and mapped into I⁰.
Source: Stacks Project, Tag 03P2 and Tag 01FD, augmentation beta.
(blueprint: def-pbc-etale-additive-cech-normalization) -/
noncomputable def additiveCechBeta {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :
    (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n →
      (additiveCechTotal U I).X n := fun x ↦
  let b : AddCommGrpCat.of
      (ULift.{u + 1} ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n)) ⟶
      ((cechComplexFunctor U).obj
        ((additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X 0).obj)).X n :=
    Pi.lift (fun y : Fin (n + 1) → ι ↦ AddCommGrpCat.ofHom
      { toFun := fun x ↦ (I.ι.f 0).hom.app
          (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))
          (ULift.up ((X.restrictFunctorΓ.inv.app (op (∏ᶜ fun l ↦ U (y l)))).hom
            (TopCat.Presheaf.cechComplexFunctorπ U
              (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) n y x.down)))
        map_zero' := by
          simp only [ULift.zero_down, map_zero]
          change ((I.ι.f 0).hom.app _) 0 = 0
          exact map_zero _
        map_add' := by
          intro x y
          simp only [ULift.add_down, map_add]
          change ((I.ι.f 0).hom.app _) (_ + _) = _
          exact map_add _ _ _ })
  (etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).ιTotal
    (.up ℕ) n 0 n (by simp) (b (ULift.up x))

/-- An edge equivalence has the alpha/beta normalization on every resolution.
This predicate uses actual augmentation components and normalized Ext cocycles;
it has no scalar or inverse-image compatibility built into it.
Source: Stacks Project, Tag 01FD, commuting augmented double-complex diagram.
(blueprint: def-pbc-etale-additive-cech-normalization) -/
def IsEtaleAdditiveCechNormalized {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (n : ℕ)
    (a : Sheaf.H X.etaleAdditiveSheaf n ≃+
      (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homology n) : Prop :=
  ∀ (I : InjectiveResolution X.etaleAdditiveSheaf)
    (c : Etale.ResolutionSectionCanonicalComparison X.etaleAdditiveSheaf I)
    (s : (additiveCechGlobal I).cycles n)
    (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n)
    (tα tβ : (additiveCechTotal U I).cycles n),
    (additiveCechTotal U I).iCycles n tα =
      additiveCechAlpha U I n ((additiveCechGlobal I).iCycles n s) →
    (additiveCechTotal U I).iCycles n tβ = additiveCechBeta U I n
      ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z) →
    (additiveCechTotal U I).homologyπ n tα =
      (additiveCechTotal U I).homologyπ n tβ →
    a (c.globalEquiv n ((additiveCechGlobal I).homologyπ n s)) =
      (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homologyπ n z

end AlgebraicGeometry.Scheme.Modules
