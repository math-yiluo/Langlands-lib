/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.Algebra.Homology.HomComplexShiftLeft

/-! # Left-argument shift comparison for internal derived Hom
Source: Stacks Project, Cohomology on Sites, Section 21.34 (Tag 0A8X)
and Section 21.35 (Tag 08JA); the signed shift calculation is written here.
(blueprint: lem-pur-derived-internal-hom-shift-left).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Shifting the source argument by m shifts internal Hom by -m.
Proof: Represent P by L and the second variable by a functorial K-injective I.
The signed reindexing of Hom(L,I)[-m] to Hom(L[m],I) sends the component in
index p and degree k to (-1)^(m*k) times the component in index p+m.
The inverse reindexes backwards with the same sign. The differential identity
follows by comparing the postcomposition and precomposition terms: their
relative sign is (-1)^m, canceled by the adjacent-degree scalar ratio.
Postcomposition commutes with reindexing and scalar multiplication. Localize
this natural chain isomorphism and use the representative comparison for
internal derived Hom. Quasi-isomorphism invariance descends the comparison
and its naturality to the derived category. The construction also works for
negative m and zero objects; m=0 has identity reindexing and signs.
Source: Stacks Project, sites-cohomology.tex, Sections 21.34 and 21.35,
Tags 0A8X and 08JA.
(blueprint: lem-pur-derived-internal-hom-shift-left) -/
theorem derivedInternalHom_shift_left
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (P : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) (m : ℤ) :
    Nonempty (
      ((Functor.curry.obj (derivedInternalHom.{u, w} (C := C) J R)).obj (op P) ⋙
        shiftFunctor _ (-m)) ≅
      ((Functor.curry.obj (derivedInternalHom.{u, w} (C := C) J R)).obj (op (P⟦m⟧)))) := by
  classical
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let F := Functor.curry.obj (derivedInternalHom.{u, w} J R)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  have rep (L : CochainComplex A ℤ) :
      Nonempty (Q ⋙ F.obj (op (Q.obj L)) ≅
        I ⋙ (homComplexFunctor (R := R)).obj (op L) ⋙ Q) := by
    obtain ⟨e⟩ := derivedInternalHom_comparison.{u, w} J R I
      (CochainComplex.toKInjectiveResolution.{u} A) (fun M ↦
        ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
          CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩)
    refine ⟨NatIso.ofComponents (fun M ↦ e.app (op L, M)) ?_⟩
    intro M N f
    simpa only [F, Q, Functor.curry_obj_obj_map, Functor.comp_map, Functor.prod_map,
      Functor.prod_obj, Functor.op_map, Functor.map_id, Functor.id_map, Functor.id_obj,
      Functor.uncurry_obj_map, NatTrans.id_app, Category.id_comp, unop_id, op_id,
      Functor.comp_obj, Functor.op_obj, Functor.uncurry_obj_obj,
      Functor.curry_obj_obj_obj, Iso.app_hom] using
      e.hom.naturality (show (op L, M) ⟶ (op L, N) from (𝟙 _, f))
  let L := Q.objPreimage P
  let eP : Q.obj L ≅ P := Q.objObjPreimageIso P
  obtain ⟨e₁⟩ := rep L
  obtain ⟨e₂⟩ := rep (L⟦m⟧)
  obtain ⟨s⟩ := homComplex_shift_left J R L m
  let e : Q ⋙ (F.obj (op (Q.obj L)) ⋙ shiftFunctor _ (-m)) ≅
      Q ⋙ F.obj (op (Q.obj (L⟦m⟧))) :=
    Functor.isoWhiskerRight e₁ (shiftFunctor _ (-m)) ≪≫
      Functor.isoWhiskerLeft (I ⋙ (homComplexFunctor (R := R)).obj (op L))
        (Q.commShiftIso (-m)).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft I s) Q ≪≫ e₂.symm
  let t := (Localization.fullyFaithfulWhiskeringLeft Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (DerivedCategory A)).preimageIso e
  let eS : Q.obj (L⟦m⟧) ≅ P⟦m⟧ :=
    (Q.commShiftIso m).app L ≪≫ (shiftFunctor _ m).mapIso eP
  exact ⟨Functor.isoWhiskerRight (F.mapIso eP.op) (shiftFunctor _ (-m)) ≪≫
    t ≪≫ (F.mapIso eS.op).symm⟩

end CategoryTheory
