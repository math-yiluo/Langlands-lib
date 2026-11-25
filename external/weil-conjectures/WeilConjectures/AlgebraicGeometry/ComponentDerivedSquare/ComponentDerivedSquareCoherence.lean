/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

set_option linter.privateModule false

/-! # Localization preserves the ordinary component-square coherence equations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

section Identity

universe v w d
variable {A B : Type w} [Category.{v} A] [Category.{v} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
  (F : A ⥤ B) (G : B ⥤ B) (H : A ⥤ A)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derived_identity (e : F ⋙ G ≅ H ⋙ F) (i : H ≅ 𝟭 A) (j : G ≅ 𝟭 B)
    (h : ∀ M, e.hom.app M ≫ F.map (i.hom.app M) = j.hom.app (F.obj M))
    (K : DerivedCategory A) :
    (Functor.mapDerivedCategorySquareIso e).hom.app K ≫
        F.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso i ≪≫
          Functor.mapDerivedCategoryIdIso A).hom.app K) =
      (Functor.mapDerivedCategoryNatIso j ≪≫
        Functor.mapDerivedCategoryIdIso B).hom.app (F.mapDerivedCategory.obj K) := by
  have he : e ≪≫ Functor.isoWhiskerRight i F = Functor.isoWhiskerLeft F j := by
    ext M
    exact h M
  have hi := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight i F) K
  have hj := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F j) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) K
  have hv := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) K
  have ht := congr_app (Functor.mapDerivedCategoryNatIso_trans e
    (Functor.isoWhiskerRight i F)) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.id_app] at hi hj hu hv ht
  rw [he] at ht
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app K)]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% hi, hu]
  erw [Category.comp_id]
  rw [← reassoc_of% hj, hv]
  erw [Category.comp_id]
  exact ht.symm

end Identity

section Composition

universe v w d
variable {A B C D E H : Type w}
  [Category.{v} A] [Category.{v} B] [Category.{v} C]
  [Category.{v} D] [Category.{v} E] [Category.{v} H]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian H]
  [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B] [HasDerivedCategory.{d} C]
  [HasDerivedCategory.{d} D] [HasDerivedCategory.{d} E] [HasDerivedCategory.{d} H]
  (a : A ⥤ B) (b : C ⥤ D) (c : E ⥤ H)
  (f : B ⥤ D) (g : D ⥤ H) (fg : B ⥤ H)
  (h : A ⥤ C) (k : C ⥤ E) (hk : A ⥤ E)
  [a.Additive] [b.Additive] [c.Additive] [f.Additive] [g.Additive] [fg.Additive]
  [h.Additive] [k.Additive] [hk.Additive]
  [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [PreservesFiniteLimits b] [PreservesFiniteColimits b]
  [PreservesFiniteLimits c] [PreservesFiniteColimits c]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]
  [PreservesFiniteLimits fg] [PreservesFiniteColimits fg]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]
  [PreservesFiniteLimits k] [PreservesFiniteColimits k]
  [PreservesFiniteLimits hk] [PreservesFiniteColimits hk]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end Composition

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
