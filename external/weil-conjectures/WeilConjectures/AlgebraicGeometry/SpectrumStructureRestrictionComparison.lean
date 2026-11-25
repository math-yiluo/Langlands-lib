/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import all WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedLocalizations
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedRestrictionSquare
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Structure and restriction comparisons for a spectrum presentation

Source: Stacks Project, Tag 08DC; Mathlib exact functors and scheme-module restriction.
(blueprint: lem-sc-spectrum-structure-restriction-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

-- Conjugate a functor square abstractly, without unfolding the derived equivalences.
private noncomputable def spectrumRestriction_conjugateIso
    {C D E F G H : Type*}
    [Category C] [Category D] [Category E] [Category F] [Category G] [Category H]
    (e : C ⥤ D) (LS : C ⥤ E) (LX : D ⥤ F)
    (dV : E ≌ G) (dU : F ≌ H) (eO : E ≌ F) (hO : e ⋙ LX ≅ LS ⋙ eO.functor) :
    e ⋙ (LX ⋙ dU.functor) ≅
      (LS ⋙ dV.functor) ⋙ ((dV.symm.trans eO).trans dU).functor := by
  let b : e ⋙ (LX ⋙ dU.functor) ≅ (LS ⋙ eO.functor) ⋙ dU.functor :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight hO _
  let c : (LS ⋙ dV.functor) ⋙ ((dV.symm.trans eO).trans dU).functor ≅
      (LS ⋙ eO.functor) ⋙ dU.functor :=
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _
      ((Functor.associator dV.functor (dV.inverse ⋙ eO.functor) dU.functor).symm ≪≫
        isoWhiskerRight
          ((Functor.associator dV.functor dV.inverse eO.functor).symm ≪≫
            isoWhiskerRight dV.unitIso.symm eO.functor ≪≫ Functor.leftUnitor _)
          dU.functor) ≪≫
    (Functor.associator _ _ _).symm
  exact b ≪≫ c.symm

-- The structure-complex comparison is independent of the chosen open subschemes.
private theorem spectrumStructure_modelIso
    (A : Type u) [CommRing A] (X : Scheme.{u}) (s : Spec (.of A) ≅ X)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (e : schemeDerivedCategory (Spec (.of A)) ≌ schemeDerivedCategory X)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    Nonempty (e.functor.obj (koszulOpenStructure A) ≅ DerivedCategory.Q.obj
      (HomologicalComplex.tensorUnit
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))) := by
  classical
  let := SheafOfModules.monoidalCategory X.sheaf
  let := (SheafOfModules.tensorClosed X.sheaf).1.some
  let M := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let N := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let S := (HomologicalComplex.single M (.up ℤ) 0).obj
    (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace))
  let k : (((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj
      (((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)).extend
        ComplexShape.embeddingDownNat)) ≅ S :=
    ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).mapIso
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (ModuleCat.of A A) 0 0 rfl) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex (koszulOpenTilde A) (.up ℤ) 0).app
      (ModuleCat.of A A) ≪≫
    (HomologicalComplex.single M (.up ℤ) 0).mapIso tildeSelf
  let e₀ := moduleIsoEquivalence s
  have : e₀.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have : e₀.functor.Additive := Functor.additive_of_preserves_binary_products _
  let b : e₀.functor ≅ Modules.restrictFunctor s.inv :=
    Adjunction.leftAdjointUniq e₀.toAdjunction (Modules.restrictAdjunction s.inv)
  let z : e₀.functor.obj
      (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) ≅
      SheafOfModules.unit (moduleRings X.toRingedSpace) :=
    b.app _ ≪≫ Modules.restrictUnitIso s.inv
  let j : (e₀.functor.mapHomologicalComplex (.up ℤ)).obj S ≅
      HomologicalComplex.tensorUnit N (.up ℤ) :=
    (HomologicalComplex.singleMapHomologicalComplex e₀.functor (.up ℤ) 0).app _ ≪≫
      (HomologicalComplex.single N (.up ℤ) 0).mapIso z
  exact ⟨e.functor.mapIso (DerivedCategory.Q.mapIso k) ≪≫
    he.app S ≪≫ DerivedCategory.Q.mapIso j⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
/-- Isomorphism transport identifies the spectrum structure complex and the full
restriction functor, including transport from localized sites to open subschemes.
Source: Stacks Project, Tag 08DC (equation-comparison, structure object);
Mathlib Algebra.Homology.DerivedCategory.ExactFunctor and
AlgebraicGeometry.Modules.Sheaf (formal isomorphism transport).
(blueprint: lem-sc-spectrum-structure-restriction-comparison).

Proof:
1. The exact equivalence Modules.overEquiv on the spectrum open transfers its chosen
   localized-site derived category to a derived category on the open subscheme in
   the same morphism universe. This is localization transported through an exact
   equivalence; the construction uses no points and applies to the empty open.
2. HomologicalComplex.extendSingleIso identifies the extended A[0] in
   koszulOpenStructure with the integer single complex. The singleMapHomologicalComplex
   comparison and tildeSelf identify its termwise tilde with O_Spec(A)[0].
   Pushforward along s identifies O_Spec(A) with O_X: identify that pushforward with
   restriction along s.inv by uniqueness of left adjoints and use
   Modules.restrictUnitIso. Apply the single-complex functor and localization, then
   use he on the structure complex. This gives the first displayed isomorphism.
3. Apply exists_scheme_iso_derived_restriction_square to s, e and he at U.
   The derived equivalences of Modules.overEquiv on both opens conjugate the
   localized-site equivalence to an equivalence G of open-subscheme derived
   categories. Functor.mapDerivedCategoryCompIso identifies the localization of
   each composite with the composite of its localizations. Whisker the restriction
   square with these equivalences and cancel their units and counits. The result
   is the displayed natural isomorphism of full restriction functors. This step
   uses no quasi-coherence, perfection, compactness or boundedness hypothesis. -/
theorem exists_spectrum_structure_restriction_comparison
    (A : Type u) [CommRing A] (X : Scheme.{u}) (s : Spec (.of A) ≅ X)
    (U : X.Opens) (V : (Spec (.of A)).Opens) (hV : s.hom ⁻¹ᵁ U = V)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (e : schemeDerivedCategory (Spec (.of A)) ≌ schemeDerivedCategory X)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let T := HomologicalComplex.tensorUnit
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    ∃ hV : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)),
      letI := hV
      ∃ G : DerivedCategory (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) ≌
        DerivedCategory (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
        Nonempty (e.functor.obj (koszulOpenStructure A) ≅ DerivedCategory.Q.obj T) ∧
        Nonempty (e.functor ⋙
          ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
              (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
              (Modules.overEquiv U)).mapDerivedCategory ≅
          ((SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) V) ⋙
            Equivalence.functor
              (C := SheafOfModules.{u}
                ((moduleRings (Spec (.of A)).toRingedSpace).over V))
              (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
              (Modules.overEquiv V)).mapDerivedCategory ⋙ G.functor) := by
  classical
  subst V
  obtain ⟨eO, ⟨hO⟩⟩ := exists_scheme_iso_derived_restriction_square s e he U
  let V := s.hom ⁻¹ᵁ U
  let EV : SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V) ≌
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) := Modules.overEquiv V
  -- Reuse the site instances throughout the derived equivalence comparisons.
  let : Abelian (SheafOfModules.{u}
      ((moduleRings (Spec (.of A)).toRingedSpace).over V)) := inferInstance
  let : Abelian (SheafOfModules.{u}
      (moduleRings V.toScheme.toRingedSpace)) := inferInstance
  let : Abelian (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over U)) := inferInstance
  let : Abelian (SheafOfModules.{u}
      (moduleRings U.toScheme.toRingedSpace)) := inferInstance
  let hLoc := Classical.choice (hasDerivedCategory_of_equivalence EV.symm)
  let := hLoc
  let EU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Modules.overEquiv U
  have : EV.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have : EV.inverse.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have : EU.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have : EU.inverse.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have : EV.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : EV.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have : EU.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : EU.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let dV := EV.mapDerivedCategory
  let dU := EU.mapDerivedCategory
  let G := (dV.symm.trans eO).trans dU
  refine ⟨hLoc, G, ?_, ?_⟩
  · exact spectrumStructure_modelIso A X s e he
  · let LS := SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) V
    let LX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
    exact ⟨isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso LX EU.functor).symm ≪≫
      spectrumRestriction_conjugateIso e.functor LS.mapDerivedCategory LX.mapDerivedCategory
        dV dU eO hO ≪≫
      isoWhiskerRight (Functor.mapDerivedCategoryCompIso LS EV.functor) G.functor⟩

end AlgebraicGeometry.Scheme
