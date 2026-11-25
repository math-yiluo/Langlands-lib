/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.Order.Directed

/-! # Invertibility from directed continuity of Hom sets

Source: Stacks Project, Tag 09RE, descending an inverse and its two equations.
(blueprint: lem-pc-directed-perfect-hom-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u v h v' h'
open CategoryTheory
namespace AlgebraicGeometry

/-- A directed system of Hom sets for two objects, with its actual limit functors.
The structure records transport, lifting and eventual equality, rather than choosing
an object or a morphism from an existence theorem.
(blueprint: lem-pc-directed-perfect-hom-iso)
-/
structure DirectedPerfectHomSystem
    (I : Type u) [Preorder I] (C : I → Type v) [∀ k, Category.{h} (C k)]
    (F : ∀ k, Bool → C k) (D : Type v') [Category.{h'} D]
    (O : Bool → D) (G : ∀ k, C k ⥤ D)
    (ψ : ∀ k b, (G k).obj (F k b) ≅ O b) where
  transport : ∀ {k l : I}, k ≤ l → ∀ {a b : Bool},
    (F k a ⟶ F k b) → (F l a ⟶ F l b)
  transport_id : ∀ {k l : I} (hkl : k ≤ l) (a : Bool),
    transport hkl (𝟙 (F k a)) = 𝟙 (F l a)
  transport_comp : ∀ {k l : I} (hkl : k ≤ l) {a b c : Bool}
    (f : F k a ⟶ F k b) (g : F k b ⟶ F k c),
    transport hkl (f ≫ g) = transport hkl f ≫ transport hkl g
  limit_transport : ∀ {k l : I} (hkl : k ≤ l) {a b : Bool}
    (f : F k a ⟶ F k b),
    (ψ l a).inv ≫ (G l).map (transport hkl f) ≫ (ψ l b).hom =
      (ψ k a).inv ≫ (G k).map f ≫ (ψ k b).hom
  lift : ∀ {a b : Bool} (f : O a ⟶ O b), ∃ (k : I) (fk : F k a ⟶ F k b),
    (ψ k a).inv ≫ (G k).map fk ≫ (ψ k b).hom = f
  equal : ∀ {k : I} {a b : Bool} (f g : F k a ⟶ F k b),
    (ψ k a).inv ≫ (G k).map f ≫ (ψ k b).hom =
      (ψ k a).inv ≫ (G k).map g ≫ (ψ k b).hom →
    ∃ (l : I) (hkl : k ≤ l), ∀ m (hlm : l ≤ m),
      transport (show k ≤ m from le_trans hkl hlm) f =
        transport (show k ≤ m from le_trans hkl hlm) g

/-- An isomorphism in the limit lifts as an isomorphism at a directed stage.
Source: Stacks Project, Tag 09RE.
Proof: lift the hom and inverse independently and transport both to a common
stage. Their composites have limit images equal to the identities. Eventual
Hom equality stabilizes these two relations. At a common upper bound the two
transported maps are mutually inverse, and the transported hom still has its
prescribed limit image.
(blueprint: lem-pc-directed-perfect-hom-iso). -/
theorem DirectedPerfectHomSystem.lift_iso
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    {C : I → Type v} [∀ k, Category.{h} (C k)]
    {F : ∀ k, Bool → C k} {D : Type v'} [Category.{h'} D]
    {O : Bool → D} {G : ∀ k, C k ⥤ D}
    {ψ : ∀ k b, (G k).obj (F k b) ≅ O b}
    (H : DirectedPerfectHomSystem I C F D O G ψ) (e : O false ≅ O true) :
    ∃ (k : I) (ek : F k false ≅ F k true),
      (ψ k false).inv ≫ (G k).map ek.hom ≫ (ψ k true).hom = e.hom := by
  obtain ⟨kf, f, hf⟩ := H.lift e.hom
  obtain ⟨kg, g, hg⟩ := H.lift e.inv
  obtain ⟨k, hfk, hgk⟩ := directed_of (· ≤ ·) kf kg
  let f' := H.transport hfk f
  let g' := H.transport hgk g
  have hf' : (ψ k false).inv ≫ (G k).map f' ≫ (ψ k true).hom = e.hom :=
    (H.limit_transport hfk f).trans hf
  have hg' : (ψ k true).inv ≫ (G k).map g' ≫ (ψ k false).hom = e.inv :=
    (H.limit_transport hgk g).trans hg
  have hfg : (ψ k false).inv ≫ (G k).map (f' ≫ g') ≫ (ψ k false).hom =
      (ψ k false).inv ≫ (G k).map (𝟙 _) ≫ (ψ k false).hom := by
    have hh := congrArg₂ (fun a b ↦ a ≫ b) hf' hg'
    simpa only [Functor.map_comp, Functor.map_id, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.id_comp,
      Category.comp_id, Iso.hom_inv_id] using hh
  have hgf : (ψ k true).inv ≫ (G k).map (g' ≫ f') ≫ (ψ k true).hom =
      (ψ k true).inv ≫ (G k).map (𝟙 _) ≫ (ψ k true).hom := by
    have hh := congrArg₂ (fun a b ↦ a ≫ b) hg' hf'
    simpa only [Functor.map_comp, Functor.map_id, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.id_comp,
      Category.comp_id, Iso.inv_hom_id] using hh
  obtain ⟨l₁, hkl₁, hl₁⟩ := H.equal (f' ≫ g') (𝟙 _) hfg
  obtain ⟨l₂, hkl₂, hl₂⟩ := H.equal (g' ≫ f') (𝟙 _) hgf
  obtain ⟨l, hl₁l, hl₂l⟩ := directed_of (· ≤ ·) l₁ l₂
  let fl := H.transport (hkl₁.trans hl₁l) f'
  let gl := H.transport (hkl₁.trans hl₁l) g'
  have hflgl : fl ≫ gl = 𝟙 _ := by
    simpa only [H.transport_comp, H.transport_id] using hl₁ l hl₁l
  have hglfl : gl ≫ fl = 𝟙 _ := by
    simpa only [H.transport_comp, H.transport_id] using hl₂ l hl₂l
  refine ⟨l, ⟨fl, gl, hflgl, hglfl⟩, ?_⟩
  exact (H.limit_transport (hkl₁.trans hl₁l) f').trans hf'

/-- Recover the comparison square from the prescribed conjugated limit image.
Source: Stacks Project, Tag 09RE, transport of the descended morphism.
(blueprint: lem-pc-directed-perfect-hom-iso)
-/
theorem iso_comparison_of_conjugated_identity
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A B : C} {T : D} (p : G.obj A ≅ T) (q : G.obj B ≅ T) (e : A ≅ B)
    (h : p.inv ≫ G.map e.hom ≫ q.hom = 𝟙 T) : p = G.mapIso e ≪≫ q := by
  apply Iso.ext
  rw [← cancel_epi p.inv]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.inv_hom_id] using h.symm

end AlgebraicGeometry
