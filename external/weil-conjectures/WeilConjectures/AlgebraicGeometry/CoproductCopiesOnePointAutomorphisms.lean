/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Logic.Equiv.Prod

/-! Automorphisms of a split scheme over a one-point base. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry

/-- Permuting the summands gives every automorphism of copies of a one-point base.
Source: blueprint lemma-artin-schreier-character-sheaf, final split-cover example.
(blueprint: new-d9-one-point-coproduct-aut)

Proof: each map from the base into the coproduct lands in a single summand, since the
base has one point. The coprojection is an open immersion, so the map factors through
that summand. The map over the base forces the factor to be the identity. Thus an
endomorphism over the base is determined by its map on points. Every permutation of
the summands is induced by reindexing the coproduct, with inverse its inverse permutation.
The action on points respects composition and therefore identifies the groups. -/
theorem coproductCopies_onePoint_aut (X : Scheme.{u}) [Subsingleton X] [Nonempty X]
    (I : Type u) :
    Nonempty (Aut (Over.mk (Sigma.desc (fun _ : I ↦ 𝟙 X))) ≃* Equiv.Perm I) := by
  classical
  let x₀ : X := Classical.choice inferInstance
  let : Unique X := ⟨⟨x₀⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let G : I → Scheme.{u} := fun _ ↦ X
  let π : (∐ G) ⟶ X := Sigma.desc (fun _ ↦ 𝟙 X)
  let C : Over X := Over.mk π
  let e : (∐ G : Scheme.{u}) ≃ I :=
    (sigmaMk G).toEquiv.symm.trans (Equiv.sigmaUnique I (fun _ ↦ X))
  have he (i : I) : e.symm i = Sigma.ι G i x₀ := by
    change sigmaMk G ⟨i, default⟩ = Sigma.ι G i x₀
    rw [sigmaMk_mk]
    exact congrArg (Sigma.ι G i) (Subsingleton.elim _ _)
  have factor (f : (∐ G) ⟶ ∐ G) (hf : f ≫ π = π) (i j : I)
      (h : (Sigma.ι G i ≫ f) x₀ = Sigma.ι G j x₀) :
      Sigma.ι G i ≫ f = Sigma.ι G j := by
    have hr : Set.range (Sigma.ι G i ≫ f) ⊆ Set.range (Sigma.ι G j) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨x₀, by simpa only [Subsingleton.elim x x₀] using h.symm⟩
    let l : X ⟶ X := IsOpenImmersion.lift (Sigma.ι G j) (Sigma.ι G i ≫ f) hr
    have hl : l ≫ Sigma.ι G j = Sigma.ι G i ≫ f :=
      IsOpenImmersion.lift_fac _ _ _
    have hid : l = 𝟙 X := by
      have hh := congrArg (fun t ↦ t ≫ π) hl
      change (l ≫ Sigma.ι G j) ≫ π = (Sigma.ι G i ≫ f) ≫ π at hh
      rw [Category.assoc, Category.assoc, hf] at hh
      have hj : Sigma.ι G j ≫ π = 𝟙 X := Sigma.ι_comp_desc _ _
      have hi : Sigma.ι G i ≫ π = 𝟙 X := Sigma.ι_comp_desc _ _
      rw [hj, hi, Category.comp_id] at hh
      exact hh
    rw [hid] at hl
    change (𝟙 X) ≫ (Sigma.ι G j : X ⟶ _) = (Sigma.ι G i : X ⟶ _) ≫ f at hl
    exact hl.symm.trans (Category.id_comp _)
  have ext (f g : C ⟶ C) (h : ∀ x : (∐ G : Scheme.{u}), f.left x = g.left x) :
      f = g := by
    apply Over.OverMorphism.ext
    apply Sigma.hom_ext
    intro i
    obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk G).surjective ((Sigma.ι G i ≫ f.left) x₀)
    rw [sigmaMk_mk] at hy
    have hy' : (Sigma.ι G i ≫ f.left) x₀ = Sigma.ι G j x₀ :=
      hy.symm.trans (congrArg (Sigma.ι G j) (@Subsingleton.elim X _ y x₀))
    have hg : (Sigma.ι G i ≫ g.left) x₀ = Sigma.ι G j x₀ := by
      change g.left (Sigma.ι G i x₀) = Sigma.ι G j x₀
      rw [← h]
      exact hy'
    exact (factor f.left (Over.w f) i j hy').trans
      (factor g.left (Over.w g) i j hg).symm
  let F := Over.forget X ⋙ Scheme.forgetToTop ⋙ forget TopCat
  let ρ : Aut C →* Equiv.Perm I :=
    e.permCongrHom.toMonoidHom.comp
      (Aut.mulEquivPerm.toMonoidHom.comp (F.mapAut C))
  have hρ (a : Aut C) (i : I) : ρ a i = e (a.asIso.hom.left (e.symm i)) := rfl
  refine ⟨MulEquiv.ofBijective ρ ⟨?_, ?_⟩⟩
  · intro a b hab
    apply Aut.ext
    apply Iso.ext
    apply ext
    intro x
    apply e.injective
    have hh := congrFun (congrArg (fun q : Equiv.Perm I ↦ (q : I → I)) hab) (e x)
    rw [hρ, hρ, Equiv.symm_apply_apply] at hh
    exact hh
  · intro q
    let a : Aut C := .of (Over.isoMk (Sigma.reindex q G) (by
      change (Sigma.reindex q G).hom ≫ π = π
      apply Sigma.hom_ext
      intro i
      rw [← Category.assoc, Sigma.ι_reindex_hom q G i]
      change Sigma.ι G (q i) ≫ π = Sigma.ι G i ≫ π
      exact (Sigma.ι_comp_desc (fun _ : I ↦ 𝟙 X) (q i)).trans
        (Sigma.ι_comp_desc (fun _ : I ↦ 𝟙 X) i).symm))
    refine ⟨a, ?_⟩
    ext i
    rw [hρ, he]
    have hh := congrArg (fun t : X ⟶ ∐ G ↦ t x₀) (Sigma.ι_reindex_hom q G i)
    change (Sigma.ι G i ≫ (Sigma.reindex q G).hom) x₀ = _ at hh
    change e ((Sigma.ι G i ≫ (Sigma.reindex q G).hom) x₀) = q i
    rw [hh, ← he]
    exact e.apply_symm_apply _

end AlgebraicGeometry
