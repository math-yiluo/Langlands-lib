/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The left unit law for exact restriction on derived categories
Source: Stacks Project, Cohomology on Sites, Tag 0D6E.
(blueprint: lem-pbc-exact-restriction-derived-identity-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private theorem invertNormalizedSquare {C D E : Type*}
    [Category C] [Category D] [Category E] (P : C ⥤ E) (Q : D ⥤ E)
    {B₁ B₂ : C} {T₁ T₂ : D} {U V : E}
    (b : B₁ ≅ B₂) (t : T₁ ≅ T₂) (e : P.obj B₁ ≅ V)
    (a : U ≅ Q.obj T₁) (u : Q.obj T₂ ⟶ P.obj B₂) (v : U ⟶ V)
    (h : u ≫ P.map b.inv ≫ e.hom = Q.map t.inv ≫ a.inv ≫ v) :
    v ≫ e.inv ≫ P.map b.hom = a.hom ≫ Q.map t.hom ≫ u := by
  have hh := congrArg (fun k ↦ a.hom ≫ Q.map t.hom ≫ k ≫ e.inv ≫ P.map b.hom) h
  simp only [Category.assoc, ← P.map_comp, ← Q.map_comp_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, Iso.hom_inv_id_assoc] at hh
  erw [Q.map_id, Category.id_comp, Iso.hom_inv_id_assoc,
    P.map_id, Category.comp_id] at hh
  exact hh.symm

/-- An ordinary left unit comparison induces the corresponding derived left unit comparison.
Source: Stacks 0D6E; the exact-derived composition and unit laws.
(blueprint: lem-pbc-exact-restriction-derived-identity-unit).

Proof: the componentwise hypothesis identifies the comparison with the whiskering of
`e` followed by the left unitor. Functoriality on natural isomorphisms, compatibility
with whiskering, and the exact-derived left unit law identify the two maps. -/
theorem exactRestrictionDerivedIdentityUnit {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (U : C ⥤ C) [F.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : U ≅ 𝟭 C) (a : U ⋙ F ≅ F)
    (ha : ∀ X, a.hom.app X = F.map (e.hom.app X)) (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryCompIso U F ≪≫
      Functor.mapDerivedCategoryNatIso a).hom.app K =
      F.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app K)
      := by
  have heq : a = Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F := by
    apply Iso.ext
    ext X
    change a.hom.app X = F.map (e.hom.app X) ≫ 𝟙 _
    erw [Category.comp_id]
    exact ha X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e F) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) K
  have hi : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor F)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  rw [heq]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hn hu
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_trans, hi, Category.comp_id, Functor.map_comp]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso U F).inv.app K),
    Iso.inv_hom_id_app_assoc, ← reassoc_of% hn, hu]
  exact (Category.comp_id _).symm

end CategoryTheory
