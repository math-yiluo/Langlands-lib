/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.OpenUnionRestrictionComparisonData
import WeilConjectures.AlgebraicGeometry.OpenUnionRestrictionComparisonCoherence

/-! # Canonical comparison diagram on inverse image opens of an open union

Source: Stacks Project, Tag 08BW, restriction to the union before applying exactness.
(blueprint: lem-sc-open-union-restriction-comparison-diagram).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option linter.style.haveILetI false in
-- Inline the localization witnesses as in the dependent statement, avoiding costly conversion.
-- Specializing the two comparisons over dependent localizations needs this limit.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Canonical comparison diagram for restriction through an open union.
Source: Stacks Project Tag 08BW, canonical restriction diagram; Mathlib
`Modules.overMapCompOverEquiv`, `overFunctorEquiv`, `restrictFunctorComp`, and
`restrictFunctorCongr`.
(blueprint: lem-sc-open-union-restriction-comparison-diagram).

Proof: Identify the inverse images U, T, and their intersection under the union
inclusion with W, V, and their intersection by the canonical image isomorphisms.
Transport the given derived localizations in Hom universe w along the exact
module equivalences of these scheme isomorphisms. Use their induced derived
equivalences for eW, eV, and eI. Compare restriction along each chain of open
inclusions using overMapCompOverEquiv and the counit of overEquiv, followed by
restrictFunctorComp and restrictFunctorCongr. Derive these natural isomorphisms
to obtain qW, qV, cW, cV, and qI. The two pasting identities hold underived by
componentwise cancellation of the image isomorphisms and the overEquiv units
and counits. On complexes use mapDerivedCategoryCompIso_fac and
mapDerivedCategoryNatIso_fac, then Localization.natTrans_ext to extend the
identities to the derived categories. No local morphisms or compatibility
hypothesis occur here. The construction also works for empty and disjoint
opens: all identifications are isomorphisms of the corresponding empty schemes.
-/
theorem open_union_restriction_comparison_diagram
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    :
    let L := (schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let sW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let sV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    let PW := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).mapDerivedCategory
    let PV := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ W ⊔ V)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_right : V ⟶ W ⊔ V)
    let U := (W ⊔ V).ι ⁻¹ᵁ W
    let T := (W ⊔ V).ι ⁻¹ᵁ V
      ∃ hU : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
      letI := hU
      ∃ hT : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace)),
      letI := hT
      ∃ hI : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings (U ⊓ T).toScheme.toRingedSpace)),
      letI := hI
      let RU := (schemeOpenRestriction (W ⊔ V).toScheme U).mapDerivedCategory
      let RT := (schemeOpenRestriction (W ⊔ V).toScheme T).mapDerivedCategory
      let SU := (schemeOpenOverlapRestriction (W ⊔ V).toScheme
        (homOfLE inf_le_left : U ⊓ T ⟶ U)).mapDerivedCategory
      let ST := (schemeOpenOverlapRestriction (W ⊔ V).toScheme
        (homOfLE inf_le_right : U ⊓ T ⟶ T)).mapDerivedCategory
      let tU := schemeDerivedOpenRestrictionCompIso (W ⊔ V).toScheme
        (homOfLE inf_le_left : U ⊓ T ⟶ U)
      let tT := schemeDerivedOpenRestrictionCompIso (W ⊔ V).toScheme
        (homOfLE inf_le_right : U ⊓ T ⟶ T)
      ∃ (eW : schemeDerivedCategory U.toScheme ≌ schemeDerivedCategory W.toScheme)
        (eV : schemeDerivedCategory T.toScheme ≌ schemeDerivedCategory V.toScheme)
        (qW : RU ⋙ eW.functor ≅ PW) (qV : RT ⋙ eV.functor ≅ PV),
      ∃ (eI : schemeDerivedCategory (U ⊓ T).toScheme ≌
          schemeDerivedCategory (W ⊓ V).toScheme)
        (cW : SU ⋙ eI.functor ≅ eW.functor ⋙ SW)
        (cV : ST ⋙ eI.functor ≅ eV.functor ⋙ SV)
        (qI : (L ⋙ (schemeOpenRestriction (W ⊔ V).toScheme (U ⊓ T)).mapDerivedCategory) ⋙
          eI.functor ≅ (schemeOpenRestriction X (W ⊓ V)).mapDerivedCategory),
      (∀ G : schemeDerivedCategory X,
        eI.functor.map (tU.inv.app (L.obj G)) ≫ cW.hom.app (RU.obj (L.obj G)) ≫
          SW.map (qW.hom.app (L.obj G)) ≫ SW.map (kW.hom.app G) ≫ sW.hom.app G =
            qI.hom.app G) ∧
      (∀ G : schemeDerivedCategory X,
        eI.functor.map (tT.inv.app (L.obj G)) ≫ cV.hom.app (RT.obj (L.obj G)) ≫
          SV.map (qV.hom.app (L.obj G)) ≫ SV.map (kV.hom.app G) ≫ sV.hom.app G =
            qI.hom.app G) := by
  classical
  rename_i dX dW dV dWV dY
  have h := open_union_restriction_comparison_data.{u, w} X W V
  refine h.imp ?_
  intro hU h
  letI := hU
  refine h.imp ?_
  intro hT h
  letI := hT
  refine h.imp ?_
  intro hI h
  letI := hI
  refine h.imp ?_
  intro eW h
  refine h.imp ?_
  intro eV h
  refine h.imp ?_
  intro qW h
  refine h.imp ?_
  intro qV h
  obtain ⟨eI, ⟨qIY⟩⟩ := h
  refine ⟨eI, ?_⟩
  exact @open_union_restriction_comparison_coherence.{u, w}
    X W V dX dW dV dWV dY hU hT hI eW eV qW qV eI qIY

end AlgebraicGeometry.Scheme
