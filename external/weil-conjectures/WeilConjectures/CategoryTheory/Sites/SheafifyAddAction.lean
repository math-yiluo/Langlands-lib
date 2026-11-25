/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Extending a presheaf action through sheafification

Source: Stacks Project, Tag 00WH; finite-product preservation of sheafification.
(blueprint: lem-sc-sheafify-add-action).
-/

@[expose] public section

universe v u w
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type w)] (G : Sheaf J AddCommGrpCat.{w}) (P : Cᵒᵖ ⥤ Type w)
    [Presheaf.IsLocallyInjective J (toSheafify J P)]
    [Presheaf.IsLocallySurjective J (toSheafify J P)]

/-- Extending an action through sheafification.
Source: Stacks Project, Tag 00WH; local bijectivity of the associated-sheaf unit.
(blueprint: lem-sc-sheafify-add-action)

Proof: Local injectivity of the unit and separatedness show that translating two
representatives with the same image gives the same image. For a section x of the
associated sheaf and a group section g, take the covering image sieve of x. On
that sieve translate each local representative by the restriction of g. The
preceding independence proves compatibility, so these images glue uniquely.
The glued section has the expected formula after every restriction on every
representative, by applying separatedness on the pulled-back image sieve.
This formula characterizes the glued section uniquely. Define the operation by
this unique section. Naturality, zero and addition follow from its characterizing
formula and the corresponding identities for the presheaf action. Any other
natural operation with the unit formula satisfies the same characterization,
and therefore is equal to it. The construction works without local nonemptiness,
including empty covers and the zero group. -/
theorem existsUnique_sheafify_add_action
    (a : ∀ U, G.obj.obj U → P.obj U → P.obj U)
    (hz : ∀ U t, a U 0 t = t)
    (ha : ∀ U g h t, a U (g + h) t = a U g (a U h t))
    (hn : ∀ ⦃U V⦄ (f : U ⟶ V) g t,
      P.map f (a U g t) = a V (G.obj.map f g) (P.map f t)) :
    ∃! b : ∀ U, G.obj.obj U → (sheafify J P).obj U → (sheafify J P).obj U,
      (∀ U t, b U 0 t = t) ∧
      (∀ U g h t, b U (g + h) t = b U g (b U h t)) ∧
      (∀ ⦃U V⦄ (f : U ⟶ V) g t,
        (sheafify J P).map f (b U g t) =
          b V (G.obj.map f g) ((sheafify J P).map f t)) ∧
      (∀ U g t, b U g ((toSheafify J P).app U t) =
        (toSheafify J P).app U (a U g t)) := by
  classical
  let Q := sheafify J P
  let η := toSheafify J P
  have hs : Presieve.IsSheaf J Q :=
    (isSheaf_iff_isSheaf_of_type J Q).mp ((presheafToSheaf J (Type w)).obj P).property
  have heq (U : Cᵒᵖ) (g : G.obj.obj U) (p q : P.obj U)
      (hpq : η.app U p = η.app U q) :
      η.app U (a U g p) = η.app U (a U g q) := by
    apply (hs _ (Presheaf.equalizerSieve_mem J η p q hpq)).isSeparatedFor.ext
    intro V f hf
    rw [← NatTrans.naturality_apply η, ← NatTrans.naturality_apply η, hn, hn, hf]
  have hex (U : Cᵒᵖ) (g : G.obj.obj U) (x : Q.obj U) :
      ∃! y : Q.obj U, ∀ (V : Cᵒᵖ) (f : U ⟶ V) (p : P.obj V),
        η.app V p = Q.map f x → Q.map f y = η.app V (a V (G.obj.map f g) p) := by
    let R := Presheaf.imageSieve η x
    have hR : R ∈ J U.unop := Presheaf.imageSieve_mem J η x
    let z : Presieve.FamilyOfElements Q R.arrows := fun V f hf ↦
      η.app _ (a _ (G.obj.map f.op g) hf.choose)
    have hzcomp : z.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro V W f k hf
      dsimp [z]
      rw [← NatTrans.naturality_apply η, hn]
      have hgg : G.obj.map k.op (G.obj.map f.op g) = G.obj.map (k ≫ f).op g := by
        simp
      rw [hgg]
      apply heq
      rw [NatTrans.naturality_apply η, hf.choose_spec]
      exact (by simpa using (R.downward_closed hf k).choose_spec)
    let y := (hs R hR).amalgamate z hzcomp
    have hy : z.IsAmalgamation y := (hs R hR).isAmalgamation hzcomp
    refine ⟨y, ?_, ?_⟩
    · intro V f p hp
      apply (hs _ (J.pullback_stable f.unop hR)).isSeparatedFor.ext
      intro W k hk
      change R (k ≫ f.unop) at hk
      rw [← ConcreteCategory.comp_apply, ← Q.map_comp]
      change Q.map (k ≫ f.unop).op y = _
      rw [hy _ hk]
      dsimp [z]
      rw [← NatTrans.naturality_apply η, hn]
      have hgg : G.obj.map k.op (G.obj.map f g) =
          G.obj.map (k ≫ f.unop).op g := by simp
      rw [hgg]
      apply heq
      rw [hk.choose_spec, NatTrans.naturality_apply η, hp]
      simp only [op_comp, Functor.map_comp]
      rfl
    · intro y' hy'
      apply (hs R hR).isSeparatedFor.ext
      intro V f hf
      rw [hy' _ f.op hf.choose hf.choose_spec, hy _ hf]
  let b : ∀ U, G.obj.obj U → Q.obj U → Q.obj U := fun U g x ↦ (hex U g x).choose
  have bm (U : Cᵒᵖ) (g : G.obj.obj U) (x : Q.obj U)
      (V : Cᵒᵖ) (f : U ⟶ V) (p : P.obj V) (hp : η.app V p = Q.map f x) :
      Q.map f (b U g x) = η.app V (a V (G.obj.map f g) p) :=
    (hex U g x).choose_spec.1 V f p hp
  have bq : ∀ U g p, b U g (η.app U p) = η.app U (a U g p) := by
    intro U g p
    simpa using bm U g (η.app U p) U (𝟙 U) p (by simp)
  have bn : ∀ ⦃U V⦄ (f : U ⟶ V) g x,
      Q.map f (b U g x) = b V (G.obj.map f g) (Q.map f x) := by
    intro U V f g x
    apply (hex V (G.obj.map f g) (Q.map f x)).choose_spec.2
    intro W k p hp
    rw [← ConcreteCategory.comp_apply, ← Q.map_comp]
    have hp' : η.app W p = Q.map (f ≫ k) x := by simpa using hp
    rw [bm U g x W (f ≫ k) p hp']
    simp
  have bz : ∀ U x, b U 0 x = x := by
    intro U x
    symm
    apply (hex U 0 x).choose_spec.2
    intro V f p hp
    rw [map_zero, hz]
    exact hp.symm
  have ba : ∀ U g h x, b U (g + h) x = b U g (b U h x) := by
    intro U g h x
    symm
    apply (hex U (g + h) x).choose_spec.2
    intro V f p hp
    rw [bn, bm U h x V f p hp, bq, map_add, ha]
  refine ⟨b, ⟨bz, ba, bn, bq⟩, ?_⟩
  intro c hc
  funext U g x
  apply (hex U g x).choose_spec.2
  intro V f p hp
  rw [hc.2.2.1, ← hp, hc.2.2.2]


end CategoryTheory

