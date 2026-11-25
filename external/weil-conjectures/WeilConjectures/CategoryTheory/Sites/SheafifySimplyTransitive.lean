/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Simple transitivity after sheafification

Source: Stacks Project, Tags 03AH and 00WH; local representations and sheaf gluing.
(blueprint: lem-sc-sheafify-simply-transitive).
-/

@[expose] public section

universe v u w
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type w)] (G : Sheaf J AddCommGrpCat.{w}) (P : Cᵒᵖ ⥤ Type w)
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Presheaf.IsLocallyInjective J (toSheafify J P)]
    [Presheaf.IsLocallySurjective J (toSheafify J P)]

/-- Simple transitivity passes to sheafification.
Source: Stacks Project, Tags 03AH and 00WH; local bijectivity and sheaf gluing.
(blueprint: lem-sc-sheafify-simply-transitive)

Proof: Represent a section of the associated sheaf locally in P. Equality of two
translations of this section becomes equality in P on a refinement, by local
injectivity of the unit. Naturality of the original action and its freeness give
local equality of the group sections. Separatedness of G gives global equality.
For two associated-sheaf sections, intersect their image sieves. On this cover
choose the unique group sections translating their representatives. Compatibility
with the extended operation and its just-proved freeness show that these local
group sections agree under restriction. Glue in G, and use separatedness of the
associated sheaf to verify that the glued group section translates the first
section to the second. No nonemptiness hypothesis is needed; both sections are
given. Empty covers and zero groups satisfy the same argument. -/
theorem bijective_sheafify_add_action
    (a : ∀ U, G.obj.obj U → P.obj U → P.obj U)
    (han : ∀ ⦃U V⦄ (f : U ⟶ V) g t,
      P.map f (a U g t) = a V (G.obj.map f g) (P.map f t))
    (hb : ∀ U t, Function.Bijective (a U · t))
    (b : ∀ U, G.obj.obj U → (sheafify J P).obj U → (sheafify J P).obj U)
    (hn : ∀ ⦃U V⦄ (f : U ⟶ V) g t,
      (sheafify J P).map f (b U g t) =
        b V (G.obj.map f g) ((sheafify J P).map f t))
    (hq : ∀ U g t, b U g ((toSheafify J P).app U t) =
      (toSheafify J P).app U (a U g t)) :
    ∀ U t, Function.Bijective (b U · t) := by
  classical
  let Q := sheafify J P
  let η := toSheafify J P
  have hs : Presieve.IsSheaf J Q :=
    (isSheaf_iff_isSheaf_of_type J Q).mp ((presheafToSheaf J (Type w)).obj P).property
  let GT := G.obj ⋙ forget AddCommGrpCat
  have hG : Presieve.IsSheaf J GT :=
    (isSheaf_iff_isSheaf_of_type J GT).mp ((sheafCompose J (forget AddCommGrpCat)).obj G).property
  have hi (U : Cᵒᵖ) (p : P.obj U) (g h : G.obj.obj U)
      (he : η.app U (a U g p) = η.app U (a U h p)) : g = h := by
    apply (hG _ (Presheaf.equalizerSieve_mem J η _ _ he)).isSeparatedFor.ext
    intro V f hf
    change G.obj.map f.op g = G.obj.map f.op h
    apply (hb _ (P.map f.op p)).injective
    dsimp only
    rw [← han, ← han]
    exact hf
  have bi (U : Cᵒᵖ) (x : Q.obj U) : Function.Injective (b U · x) := by
    intro g h he
    apply (hG _ (Presheaf.imageSieve_mem J η x)).isSeparatedFor.ext
    intro V f hf
    obtain ⟨p, hp⟩ := hf
    change G.obj.map f.op g = G.obj.map f.op h
    apply hi (Opposite.op V) p
    dsimp only at he
    rw [← hq, ← hq, hp, ← hn, ← hn]
    exact congrArg (Q.map f.op) he
  intro U x
  refine ⟨bi U x, ?_⟩
  intro y
  let R := Presheaf.imageSieve η x ⊓ Presheaf.imageSieve η y
  have hR : R ∈ J U.unop :=
    J.intersection_covering (Presheaf.imageSieve_mem J η x) (Presheaf.imageSieve_mem J η y)
  let d : Presieve.FamilyOfElements GT R.arrows := fun V f hf ↦
    ((hb (Opposite.op V) hf.1.choose).surjective hf.2.choose).choose
  have hd (V : C) (f : V ⟶ U.unop) (hf : R f) :
      b (Opposite.op V) (d f hf) (Q.map f.op x) = Q.map f.op y := by
    rw [← hf.1.choose_spec, ← hf.2.choose_spec, hq]
    congr 1
    exact ((hb (Opposite.op V) hf.1.choose).surjective hf.2.choose).choose_spec
  have hdcomp : d.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W f k hf
    change d (k ≫ f) (R.downward_closed hf k) = G.obj.map k.op (d f hf)
    apply bi (Opposite.op W) (Q.map (k ≫ f).op x)
    dsimp only
    rw [hd W (k ≫ f) (R.downward_closed hf k)]
    have hmx : Q.map (k ≫ f).op x = Q.map k.op (Q.map f.op x) := by simp
    rw [hmx, ← hn, hd V f hf]
    simp only [op_comp, Functor.map_comp]
    rfl
  let g := (hG R hR).amalgamate d hdcomp
  have hg : d.IsAmalgamation g := (hG R hR).isAmalgamation hdcomp
  refine ⟨g, ?_⟩
  apply (hs R hR).isSeparatedFor.ext
  intro V f hf
  rw [hn]
  change b (Opposite.op V) (GT.map f.op g) (Q.map f.op x) = Q.map f.op y
  rw [hg f hf]
  exact hd V f hf


end CategoryTheory

