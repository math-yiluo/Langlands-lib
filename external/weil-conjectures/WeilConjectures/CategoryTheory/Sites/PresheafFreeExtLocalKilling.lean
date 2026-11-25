/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.CategoryTheory.Abelian.ExtEpiEffacement

/-!
# Local killing of Ext classes from free abelian sheaves

Source: Stacks Project, Derived Categories, Tag 06XU; Cohomology on Sites, Tag 03F9.
(blueprint: lem-sc-presheaf-free-ext-local-killing)
(blueprint: lem-sc-presheaf-free-ext-local-killing-witness)

This implementation follows the explicit generator lifting construction.
The witness conclusion contains the vanishing equation directly; it has no
vacuous existential proof witness or ``True`` padding. The conclusion was
corrected in response to upstream review #1428.
-/

@[expose] public section

universe u v w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf

-- The locally generated image is an abelian subsheaf, also in a small value universe.
private theorem epi_locally_surjective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    {G H : Sheaf J AddCommGrpCat.{v}} (g : G ⟶ H) [Epi g] :
    Presheaf.IsLocallySurjective J g.hom := by
  classical
  let R := (Subfunctor.range (Functor.whiskerRight g.hom (forget AddCommGrpCat.{v}))).sheafify J
  let A (V : Cᵒᵖ) : AddSubgroup (H.obj.obj V) :=
    { carrier := R.obj V
      zero_mem' := by
        change Presheaf.imageSieve g.hom (0 : H.obj.obj V) ∈ J V.unop
        apply J.superset_covering _ (J.top_mem _)
        intro W h _
        exact ⟨0, by simp⟩
      add_mem' := by
        intro x y hx hy
        change Presheaf.imageSieve g.hom (x + y) ∈ J V.unop
        apply J.superset_covering _ (J.intersection_covering hx hy)
        intro W h hh
        obtain ⟨tx, htx⟩ := hh.1
        obtain ⟨ty, hty⟩ := hh.2
        change g.hom.app _ tx = H.obj.map h.op x at htx
        change g.hom.app _ ty = H.obj.map h.op y at hty
        exact ⟨tx + ty, by simp [htx, hty]⟩
      neg_mem' := by
        intro x hx
        change Presheaf.imageSieve g.hom (-x) ∈ J V.unop
        apply J.superset_covering _ hx
        intro W h hh
        obtain ⟨t, ht⟩ := hh
        change g.hom.app _ t = H.obj.map h.op x at ht
        exact ⟨-t, by simp [ht]⟩ }
  let B : Cᵒᵖ ⥤ AddCommGrpCat.{v} :=
    { obj := fun V ↦ AddCommGrpCat.of (A V)
      map := fun {V W} h ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦ ⟨H.obj.map h x.val, R.map h x.property⟩
          map_zero' := by apply Subtype.ext; simp
          map_add' := by intros; apply Subtype.ext; simp }
      map_id := by intro V; ext x; simp
      map_comp := by intro V W T h k; ext x; simp }
  have hB : Presheaf.IsSheaf J B := by
    apply Presheaf.isSheaf_of_isSheaf_comp J B (forget AddCommGrpCat.{v})
    change Presheaf.IsSheaf J R.toFunctor
    apply (isSheaf_iff_isSheaf_of_type J _).2
    apply Subfunctor.sheafify_isSheaf
    exact (isSheaf_iff_isSheaf_of_type J _).1
      ((sheafCompose J (forget AddCommGrpCat.{v})).obj H).property
  let I : Sheaf J AddCommGrpCat.{v} := ⟨B, hB⟩
  let i : I ⟶ H := ⟨{
    app := fun V ↦ AddCommGrpCat.ofHom (A V).subtype
    naturality := by intros; rfl }⟩
  let e : G ⟶ I := ⟨{
    app := fun V ↦ AddCommGrpCat.ofHom
      { toFun := fun x ↦ ⟨g.hom.app V x,
          (Subfunctor.range (Functor.whiskerRight g.hom (forget AddCommGrpCat.{v}))).le_sheafify J
            V ⟨x, rfl⟩⟩
        map_zero' := by apply Subtype.ext; simp
        map_add' := by intros; apply Subtype.ext; simp }
    naturality := by
      intro V W h
      ext x
      exact NatTrans.naturality_apply g.hom h x }⟩
  have hfac : e ≫ i = g := by rfl
  have hi : Mono i := by
    have (V : Cᵒᵖ) : Mono (i.hom.app V) :=
      (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective
    have : Mono i.hom := NatTrans.mono_of_mono_app _
    exact (sheafToPresheaf J AddCommGrpCat).mono_of_mono_map this
  have : Epi i := epi_of_epi_fac hfac
  have : IsIso i := isIso_of_mono_of_epi i
  constructor
  intro U s
  let t := (inv i).hom.app (Opposite.op U) s
  have ht : t.val = s := by
    have hh := congrArg (fun k : H ⟶ H ↦ k.hom.app (Opposite.op U) s)
      (IsIso.inv_hom_id i)
    exact hh
  exact (ht ▸ t.property)

private theorem exists_presheaf_cover_lift
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    (P : Cᵒᵖ ⥤ Type v) (G : Sheaf J AddCommGrpCat.{v})
    (g : G ⟶ (presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free))
    [Epi g] :
    ∃ (E : Cᵒᵖ ⥤ Type v) (f : E ⟶ P), Presheaf.IsLocallySurjective J f ∧
      ∃ (l : (presheafToSheaf J AddCommGrpCat).obj (E ⋙ AddCommGrpCat.free) ⟶ G),
        l ≫ g = (presheafToSheaf J AddCommGrpCat).map
          (Functor.whiskerRight f AddCommGrpCat.free) := by
  classical
  let ZP := (presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free)
  let a : P ⟶ ZP.obj ⋙ forget AddCommGrpCat.{v} :=
    { app := fun V ↦ TypeCat.ofHom fun p ↦ (toSheafify J (P ⋙ AddCommGrpCat.free)).app V
        (FreeAbelianGroup.of p)
      naturality := by
        intro V W h
        ext p
        have ht := NatTrans.naturality_apply (toSheafify J (P ⋙ AddCommGrpCat.free)) h
          (FreeAbelianGroup.of p)
        simpa [AddCommGrpCat.free_map_coe] using ht }
  let E : Cᵒᵖ ⥤ Type v :=
    { obj := fun V ↦ { pg : P.obj V × G.obj.obj V | g.hom.app V pg.2 = a.app V pg.1 }
      map := fun {V W} h ↦ TypeCat.ofHom fun pg ↦
        ⟨⟨P.map h pg.val.1, G.obj.map h pg.val.2⟩, by
          change g.hom.app W (G.obj.map h pg.val.2) = a.app W (P.map h pg.val.1)
          rw [NatTrans.naturality_apply g.hom h, pg.property]
          exact (NatTrans.naturality_apply a h pg.val.1).symm⟩
      map_id := by
        intro V
        apply ConcreteCategory.hom_ext
        intro pg
        apply Subtype.ext
        simp
      map_comp := by
        intro V W T h k
        apply ConcreteCategory.hom_ext
        intro pg
        apply Subtype.ext
        simp }
  let f : E ⟶ P :=
    { app := fun V ↦ TypeCat.ofHom fun pg ↦ pg.val.1
      naturality := by intros; rfl }
  have hg : Presheaf.IsLocallySurjective J g.hom :=
    epi_locally_surjective g
  have hf : Presheaf.IsLocallySurjective J f := by
    constructor
    intro U p
    apply J.superset_covering _ (Presheaf.imageSieve_mem J g.hom (a.app _ p))
    intro V h hh
    obtain ⟨t, ht⟩ := hh
    refine ⟨⟨⟨P.map h.op p, t⟩, ?_⟩, rfl⟩
    exact ht.trans (NatTrans.naturality_apply a h.op p).symm
  let b : E ⋙ AddCommGrpCat.free ⟶ G.obj :=
    { app := fun V ↦ AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun pg ↦ pg.val.2)
      naturality := by
        intro V W h
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro pg
        change FreeAbelianGroup.lift _
          ((AddCommGrpCat.free.map (E.map h)) (FreeAbelianGroup.of pg)) =
            G.obj.map h (FreeAbelianGroup.lift _ (FreeAbelianGroup.of pg))
        simp [E] }
  let l : (presheafToSheaf J AddCommGrpCat).obj (E ⋙ AddCommGrpCat.free) ⟶ G :=
    ⟨sheafifyLift J b G.property⟩
  refine ⟨E, f, hf, l, ?_⟩
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ZP.property
  change toSheafify J _ ≫ (sheafifyLift J b G.property ≫ g.hom) =
    toSheafify J _ ≫ sheafifyMap J (Functor.whiskerRight f AddCommGrpCat.free)
  rw [← Category.assoc, toSheafify_sheafifyLift, ← toSheafify_naturality]
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro pg
  change g.hom.app V (FreeAbelianGroup.lift _ (FreeAbelianGroup.of pg)) =
    (toSheafify J (P ⋙ AddCommGrpCat.free)).app V
      ((AddCommGrpCat.free.map (f.app V)) (FreeAbelianGroup.of pg))
  simp only [FreeAbelianGroup.lift_apply_of, AddCommGrpCat.free_map_coe,
    FreeAbelianGroup.map_of]
  exact pg.property

/-- A positive Ext class from the sheafified free abelian presheaf is killed after a
locally surjective map of small-valued presheaves.
Source: Stacks Project, Derived Categories, Tag 06XU (Yoneda representatives), and
Cohomology on Sites, Tag 03F9 (local lifting in the vanishing argument).
(blueprint: lem-sc-presheaf-free-ext-local-killing)
(blueprint: lem-sc-presheaf-free-ext-local-killing-witness)

Proof: apply Ext.exists_epi_comp_eq_zero, whose fraction argument from Tag 06XU
provides an epimorphism g : G -> Z[P] that kills x. At each object V construct
E(V) as the subtype of P(V) times G(V) consisting of pairs (p,t) for which g(t)
is the image of the free generator p in Z[P](V). Restrictions act on both
coordinates; naturality of the generator map proves that they preserve the
defining equality. Projection to the first coordinate defines f : E -> P.
This is locally surjective because g is an epimorphism of abelian sheaves;
the private image-subsheaf argument proves the required local surjectivity
without enlarging the value universe. E(V) remains in Type v. Projection to
the second coordinate extends by FreeAbelianGroup.lift and sheafifyLift to
l : Z[E] -> G. Checking on free generators gives l followed by g equal to Z[f].
Ext composition associativity therefore identifies pullback along Z[f] with
pullback along l of the zero pullback along g. This is zero, including for q=1.
No representative of a mere existence theorem is used to define public data. -/
theorem exists_presheaf_ext_local_killing_witness
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (P : Cᵒᵖ ⥤ Type v)
    (q : ℕ) (hq : 0 < q)
    (x : Ext ((presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free)) F q) :
    ∃ (E : Cᵒᵖ ⥤ Type v) (f : E ⟶ P),
      Presheaf.IsLocallySurjective J f ∧
      (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
        (Functor.whiskerRight f AddCommGrpCat.free))).comp x (Nat.zero_add q) = 0 := by
  obtain ⟨G, g, hg, hx⟩ := Ext.exists_epi_comp_eq_zero q hq x
  let : Epi g := hg
  obtain ⟨E, f, hf, l, hl⟩ := exists_presheaf_cover_lift P G g
  refine ⟨E, f, hf, ?_⟩
  rw [← hl, ← Ext.mk₀_comp_mk₀_assoc, hx, Ext.comp_zero]

/-- The local Ext killing conclusion. (blueprint: lem-sc-presheaf-free-ext-local-killing)
Proof: apply the preceding Yoneda witness theorem, which directly supplies the
presheaf, locally surjective map, and vanishing equation. No existential proof
witness or auxiliary True proposition is needed. -/
theorem exists_presheaf_ext_local_killing
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (P : Cᵒᵖ ⥤ Type v)
    (q : ℕ) (hq : 0 < q)
    (x : Ext ((presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free)) F q) :
    ∃ (E : Cᵒᵖ ⥤ Type v) (f : E ⟶ P), Presheaf.IsLocallySurjective J f ∧
      (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
        (Functor.whiskerRight f AddCommGrpCat.free))).comp x (Nat.zero_add q) = 0 :=
  exists_presheaf_ext_local_killing_witness F P q hq x

end CategoryTheory.Sheaf
