/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Composition of coherent upper shriek for proper morphisms

Source: Stacks Project, Duality for Schemes, Lemma 48.16.3 (Tag 0ATX), proper case
(blueprint: lem-sc-proper-upper-shriek-composition).
-/

@[expose] public section

universe uS wXS wYS wZS

open CategoryTheory

namespace AlgebraicGeometry

/-- Proper upper shriek composes naturally on the unbounded quasi-coherent derived
categories, with the counit of the composite identified with the two successive counits.
The restricted direct images `Rf`, `Rg`, `Rfg` on `D_QCoh` are tied to
`schemeDerivedDirectImage` by the comparison isomorphisms `eRf`, `eRg`, `eRfg`; the
comparison `c : Rg_* ∘ Rf_* ≅ R(g ∘ f)_*` is the canonical one, characterized by the
right-derived unit equation of `RingedSpace.exists_derivedModuleDirectImageComposition`
(Tag 0D5T). The right adjoints `uf`, `ug`, `ufg` with their adjunctions are the `h^!`
of the statement (def-pc-upper-shriek-right-adjoint).
Source: Stacks Project, Tag 0ATX, proper case
(blueprint: lem-sc-proper-upper-shriek-composition).

Proof:
1. `lem-pc-proper-derived-direct-image-composition` gives the canonical comparison on
   `D_QCoh`, here `c` transported along `eRf`, `eRg`, `eRfg` (the inclusions are fully
   faithful).
2. `lem-pc-noetherian-derived-direct-image-right-adjoint` supplies the right adjoints,
   as in `def-pc-upper-shriek-right-adjoint`. Compose the adjunctions for f and g and
   transport across the comparison. The uniqueness isomorphism for right adjoints
   (`lem-cat-right-adjoint-composition`) gives `(g ∘ f)^! ≅ f^! ∘ g^!`.
3. The composite-adjunction counit formula and compatibility of right-adjoint uniqueness
   with counits (`lem-cat-right-adjoint-composition`) give the displayed equality at K,
   read after the faithful inclusion into `D(𝒪_Z)`. Since the isomorphism is a functor
   isomorphism, it is natural in every K. -/
theorem exists_properUpperShriekComposition
    {X Y Z : Scheme.{uS}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [HasDerivedCategory.{wXS} (SheafOfModules.{uS} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wYS} (SheafOfModules.{uS} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wZS} (SheafOfModules.{uS} (moduleRings Z.toRingedSpace))]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g]
    (Rf : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (eRf : Rf ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (Rg : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (eRg : Rg ⋙ (schemeDerivedQCohProperty Z).ι ≅
      (schemeDerivedQCohProperty Y).ι ⋙ schemeDerivedDirectImage g)
    (Rfg : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Z)
    (eRfg : Rfg ⋙ (schemeDerivedQCohProperty Z).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage (f ≫ g))
    (c : schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g ≅
      schemeDerivedDirectImage (f ≫ g))
    (hc : ∀ K : HomotopyCategory (SheafOfModules.{uS} (moduleRings X.toRingedSpace))
        (ComplexShape.up ℤ),
      (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
          c.inv.app (DerivedCategory.Qh.obj K) =
        (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (schemeDerivedDirectImage g).map
            ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K))
    (uf : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (ug : schemeDerivedQCohCategory Z ⥤ schemeDerivedQCohCategory Y)
    (ufg : schemeDerivedQCohCategory Z ⥤ schemeDerivedQCohCategory X)
    (af : Rf ⊣ uf) (ag : Rg ⊣ ug) (afg : Rfg ⊣ ufg) :
    ∃ e : ufg ≅ ug ⋙ uf, ∀ K : schemeDerivedQCohCategory Z,
      (schemeDerivedQCohProperty Z).ι.map (Rfg.map (e.hom.app K)) ≫
          eRfg.hom.app (uf.obj (ug.obj K)) ≫
          c.inv.app ((schemeDerivedQCohProperty X).ι.obj (uf.obj (ug.obj K))) ≫
          (schemeDerivedDirectImage g).map (eRf.inv.app (uf.obj (ug.obj K))) ≫
          (schemeDerivedDirectImage g).map
            ((schemeDerivedQCohProperty Y).ι.map (af.counit.app (ug.obj K))) ≫
          eRg.inv.app (ug.obj K) ≫
          (schemeDerivedQCohProperty Z).ι.map (ag.counit.app K) =
        (schemeDerivedQCohProperty Z).ι.map (afg.counit.app K) := by
  have _canonicalComparison := hc
  let b : (Rf ⋙ Rg) ⋙ (schemeDerivedQCohProperty Z).ι ≅
      Rfg ⋙ (schemeDerivedQCohProperty Z).ι :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Rf eRg ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eRf _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ c ≪≫ eRfg.symm
  let q : Rf ⋙ Rg ≅ Rfg :=
    Functor.fullyFaithfulCancelRight (schemeDerivedQCohProperty Z).ι b
  let a : Rfg ⊣ ug ⋙ uf := (af.comp ag).ofNatIsoLeft q
  refine ⟨afg.rightAdjointUniq a, ?_⟩
  intro K
  have h := congrArg ((schemeDerivedQCohProperty Z).ι.map)
    (afg.rightAdjointUniq_hom_app_counit a K)
  simp only [a, q, Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.fullyFaithfulCancelRight_inv_app,
    Functor.map_comp, Functor.map_preimage] at h
  simp only [b, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.comp_obj] at h
  have hn := eRg.inv.naturality (af.counit.app (ug.obj K))
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn] at h
  exact h

end AlgebraicGeometry
