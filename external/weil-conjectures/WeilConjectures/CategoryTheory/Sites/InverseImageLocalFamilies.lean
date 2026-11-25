/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Locally surjective families under an inverse image

Source: Stacks Project, Sites, Tag 00WL; adjunction and local image argument.
-/

@[expose] public section

universe u v w uD vD
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

private theorem mono_injective {X Y : Sheaf J (Type w)} (f : X ⟶ Y) [Mono f]
    (U : Cᵒᵖ) : Function.Injective (f.hom.app U) := by
  let E := sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U
  have : Mono (E.map f) := inferInstance
  exact (CategoryTheory.mono_iff_injective (E.map f)).mp this

private def familySieve {ι : Type*} {A : ι → Sheaf J (Type w)}
    {B : Sheaf J (Type w)} (f : ∀ i, A i ⟶ B) {U : Cᵒᵖ}
    (x : B.obj.obj U) : Sieve U.unop where
  arrows V g := ∃ (i : ι) (y : (A i).obj.obj (op V)),
    (f i).hom.app (op V) y = B.obj.map g.op x
  downward_closed := by
    rintro V W g ⟨i, y, hy⟩ h
    refine ⟨i, (A i).obj.map h.op y, ?_⟩
    rw [NatTrans.naturality_apply, hy, op_comp, Functor.map_comp_apply]

private theorem family_factor {ι : Type*} {A : ι → Sheaf J (Type w)}
    {B : Sheaf J (Type w)} (f : ∀ i, A i ⟶ B)
    (hf : ∀ U (x : B.obj.obj U), familySieve f x ∈ J U.unop)
    {P Q : Sheaf J (Type w)} (m : P ⟶ Q) [Mono m] (g : B ⟶ Q)
    (b : ∀ i, A i ⟶ P) (hb : ∀ i, b i ≫ m = f i ≫ g) :
    ∃ t : B ⟶ P, t ≫ m = g := by
  let p := pullback.fst g m
  let E (U : Cᵒᵖ) :=
    sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U
  have hp : IsLocallySurjective p := by
    constructor
    intro U x
    apply J.superset_covering _ (hf (op U) x)
    rintro V a ⟨i, y, hy⟩
    obtain ⟨z, hz₁, hz₂⟩ := Types.exists_of_isPullback
      ((IsPullback.of_hasPullback g m).map (E (op V)))
      (B.obj.map a.op x) ((b i).hom.app (op V) y) (by
        change g.hom.app _ _ = m.hom.app _ _
        rw [← hy]
        exact (congrArg (fun k : A i ⟶ Q ↦ k.hom.app (op V) y) (hb i)).symm)
    exact ⟨z, hz₁⟩
  have : IsLocallyInjective p :=
    (isLocallyInjective_iff_injective p).mpr (mono_injective p)
  have : IsIso p := (isLocallyBijective_iff_isIso p).mp ⟨inferInstance, hp⟩
  refine ⟨inv p ≫ pullback.snd g m, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

private theorem family_map
    {D : Type uD} [Category.{vD} D] {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (G : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ G)
    {ι : Type*} {A : ι → Sheaf J (Type w)} {B : Sheaf J (Type w)}
    (f : ∀ i, A i ⟶ B)
    (hf : ∀ U (x : B.obj.obj U), familySieve f x ∈ J U.unop) :
    ∀ U (x : (L.obj B).obj.obj U),
      familySieve (fun i ↦ L.map (f i)) x ∈ K U.unop := by
  let S : Subfunctor (L.obj B).obj := ⨆ i, Subfunctor.range (L.map (f i)).hom
  let S' := S.sheafify K
  let T : Sheaf K (Type w) := ⟨S'.toFunctor,
    (isSheaf_iff_isSheaf_of_type K _).mpr
      (S.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type K _).mp (L.obj B).property))⟩
  let m : T ⟶ L.obj B := ⟨S'.ι⟩
  have : Mono m := mono_of_injective m (fun _ ↦ Subtype.val_injective)
  let b (i : ι) : L.obj (A i) ⟶ T := ⟨Subfunctor.toRange (L.map (f i)).hom ≫
    Subfunctor.homOfLe (le_trans (le_iSup (fun i ↦
      Subfunctor.range (L.map (f i)).hom) i) (S.le_sheafify K))⟩
  have hb (i : ι) : b i ≫ m = L.map (f i) := by
    ext U x
    rfl
  have : G.IsRightAdjoint := adj.isRightAdjoint
  obtain ⟨t, ht⟩ := family_factor f hf (G.map m) (adj.unit.app B)
    (fun i ↦ (adj.homEquiv _ _) (b i)) (by
      intro i
      rw [← adj.homEquiv_naturality_right, hb]
      exact (adj.unit.naturality (f i)).symm)
  let e : L.obj B ⟶ T := (adj.homEquiv _ _).symm t
  have he : e ≫ m = 𝟙 (L.obj B) := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_right]
    simpa only [e, Equiv.apply_symm_apply, Adjunction.homEquiv_id] using ht
  intro U x
  have hx : (e.hom.app U x).val = x :=
    congrArg (fun k : L.obj B ⟶ L.obj B ↦ k.hom.app U x) he
  have hmem : x ∈ S'.obj U := hx ▸ (e.hom.app U x).property
  apply K.superset_covering _ hmem
  intro V a ha
  change (L.obj B).obj.map a.op x ∈ S.obj (op V) at ha
  rw [Subfunctor.iSup_obj] at ha
  obtain ⟨i, ⟨y, hy⟩⟩ := Set.mem_iUnion.mp ha
  exact ⟨i, y, hy⟩

/-- Left adjoints between categories of sheaves of sets preserve locally surjective families.
The sites and the values may lie in independent universes.
Source: Stacks Project, Sites, Tag 00WL; adjunction and local image argument
(auxiliary; not a blueprint node).

Proof: A locally surjective family jointly lifts against monomorphisms: pull back
such a monomorphism along the proposed map, and local surjectivity makes the
pullback projection locally surjective. It is also mono, hence an isomorphism.
In the target take the subsheaf locally generated by the union of the images of
the mapped family. Each mapped arrow factors through its inclusion. By adjunction
these factorizations lift the original family against the direct image of that
inclusion, which is still mono. The joint lifting just proved factors the unit
through it. Adjunction gives a retraction of the target inclusion. Consequently
every target section lies locally in the image of one member of the mapped family.
This also handles empty families: their locally generated image is the initial
subsheaf, and all assertions are made on its covering image sieves. -/
theorem map_jointly_locally_surjective
    {D : Type uD} [Category.{vD} D] {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (G : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ G)
    {ι : Type*} {A : ι → Sheaf J (Type w)} {B : Sheaf J (Type w)}
    (f : ∀ i, A i ⟶ B)
    (hf : ∀ (U : Cᵒᵖ) (x : B.obj.obj U),
      ∃ S : Sieve U.unop, S ∈ J U.unop ∧
        ∀ (V : C) (a : V ⟶ U.unop), S a →
          ∃ (i : ι) (y : (A i).obj.obj (op V)),
            (f i).hom.app (op V) y = B.obj.map a.op x) :
    ∀ (U : Dᵒᵖ) (x : (L.obj B).obj.obj U),
      ∃ S : Sieve U.unop, S ∈ K U.unop ∧
        ∀ (V : D) (a : V ⟶ U.unop), S a →
          ∃ (i : ι) (y : (L.obj (A i)).obj.obj (op V)),
            (L.map (f i)).hom.app (op V) y = (L.obj B).obj.map a.op x := by
  have hsource U (x : B.obj.obj U) : familySieve f x ∈ J U.unop := by
    obtain ⟨S, hS, hx⟩ := hf U x
    exact J.superset_covering (fun V a ha ↦ hx V a ha) hS
  intro U x
  exact ⟨familySieve (fun i ↦ L.map (f i)) x,
    family_map L G adj f hsource U x, fun _ _ ha ↦ ha⟩

end CategoryTheory.Sheaf
