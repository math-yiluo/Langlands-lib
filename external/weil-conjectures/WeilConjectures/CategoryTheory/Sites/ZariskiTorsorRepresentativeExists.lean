/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.CategoryTheory.Sites.ZariskiTorsorFreeExtension

/-!
# A representative extension of a Zariski torsor

Source: Stacks Project, Cohomology of Sheaves, Lemma 02FQ, first construction.
(blueprint: lem-sc-zariski-torsor-representative-exists)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace CategoryTheory.Sheaf

private lemma free_generator_naturality (X : Scheme.{u})
    {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (T : G.Torsor)
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (t : T.sheaf.obj.obj U) :
    (Torsor.FreeExtension.extension X T).obj.map f
      (Torsor.FreeExtension.generator X T U t) =
        Torsor.FreeExtension.generator X T V (T.sheaf.obj.map f t) := by
  unfold Torsor.FreeExtension.generator
  have h₁ := congr_arg (fun η ↦ η
    ((toSheafify (Opens.grothendieckTopology X)
      (T.sheaf.obj ⋙ AddCommGrpCat.free)).app U (FreeAbelianGroup.of t)))
    ((Torsor.FreeExtension.generators X T).hom.naturality f)
  have h₂ := congr_arg (fun η ↦ η (FreeAbelianGroup.of t))
    ((toSheafify (Opens.grothendieckTopology X)
      (T.sheaf.obj ⋙ AddCommGrpCat.free)).naturality f)
  change (Torsor.FreeExtension.generators X T).hom.app V
    ((Torsor.FreeExtension.freeSheaf X T).obj.map f _) = _ at h₁
  change (toSheafify (Opens.grothendieckTopology X)
    (T.sheaf.obj ⋙ AddCommGrpCat.free)).app V
    (FreeAbelianGroup.map (T.sheaf.obj.map f) (FreeAbelianGroup.of t)) = _ at h₂
  rw [FreeAbelianGroup.map_of_apply] at h₂
  exact h₁.symm.trans (congr_arg ((Torsor.FreeExtension.generators X T).hom.app V) h₂.symm)

private lemma free_generator_degree (X : Scheme.{u})
    {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (T : G.Torsor)
    (U : (Opens X)ᵒᵖ) (t : T.sheaf.obj.obj U) :
    (Torsor.FreeExtension.projection X T).hom.app U
      (Torsor.FreeExtension.generator X T U t) =
        (toSheafify (Opens.grothendieckTopology X)
          (Torsor.FreeExtension.integers X)).app U ⟨1⟩ := by
  unfold Torsor.FreeExtension.generator
  change ((Torsor.FreeExtension.generators X T ≫
    Torsor.FreeExtension.projection X T).hom.app U) _ = _
  unfold Torsor.FreeExtension.projection
  rw [pushout.inl_desc]
  have h := congr_arg (fun η ↦ η.app U (FreeAbelianGroup.of t))
    (toSheafify_naturality (Opens.grothendieckTopology X)
      (Torsor.FreeExtension.augmentation X T))
  exact h.symm

private lemma free_generator_vadd (X : Scheme.{u})
    {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (T : G.Torsor)
    (U : (Opens X)ᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U) :
    Torsor.FreeExtension.generator X T U (T.vadd U g t) =
      Torsor.FreeExtension.generator X T U t +
        (Torsor.FreeExtension.inclusion X T).hom.app U g := by
  have h := congr_arg (fun η ↦ η.hom.app U
    ((toSheafify (Opens.grothendieckTopology X)
      (T.pairs ⋙ AddCommGrpCat.free)).app U
        (FreeAbelianGroup.of ((t, T.vadd U g t) : T.pairs.obj U))))
    (pushout.condition (f := Torsor.FreeExtension.difference X T)
      (g := Torsor.FreeExtension.displacement X T))
  have hd := congr_arg (fun η ↦ η.app U
    (FreeAbelianGroup.of ((t, T.vadd U g t) : T.pairs.obj U)))
    (toSheafify_naturality (Opens.grothendieckTopology X) T.pairsDiff)
  have hs := congr_arg (fun η ↦ η.app U
    (FreeAbelianGroup.of ((t, T.vadd U g t) : T.pairs.obj U)))
    (toSheafify_sheafifyLift (Opens.grothendieckTopology X) T.pairsSub G.property)
  change (Torsor.FreeExtension.generators X T).hom.app U
    ((Torsor.FreeExtension.difference X T).hom.app U _) =
      (Torsor.FreeExtension.inclusion X T).hom.app U
        ((Torsor.FreeExtension.displacement X T).hom.app U _) at h
  change (toSheafify (Opens.grothendieckTopology X)
    (T.sheaf.obj ⋙ AddCommGrpCat.free)).app U (T.pairsDiff.app U _) =
      (Torsor.FreeExtension.difference X T).hom.app U
        ((toSheafify (Opens.grothendieckTopology X)
          (T.pairs ⋙ AddCommGrpCat.free)).app U _) at hd
  change (Torsor.FreeExtension.displacement X T).hom.app U
    ((toSheafify (Opens.grothendieckTopology X)
      (T.pairs ⋙ AddCommGrpCat.free)).app U _) = T.pairsSub.app U _ at hs
  rw [← hd, hs] at h
  change (Torsor.FreeExtension.generators X T).hom.app U
    ((toSheafify (Opens.grothendieckTopology X)
      (T.sheaf.obj ⋙ AddCommGrpCat.free)).app U
      (FreeAbelianGroup.lift _ (FreeAbelianGroup.of _))) =
        (Torsor.FreeExtension.inclusion X T).hom.app U
          (FreeAbelianGroup.lift _ (FreeAbelianGroup.of _)) at h
  simp only [FreeAbelianGroup.lift_apply_of, Torsor.sub_vadd_eq, map_sub] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- A Zariski torsor is the fibre over one of an extension by the integer sheaf.

Source: Stacks Project, Cohomology of Sheaves, Lemma 02FQ, first construction
(https://stacks.math.columbia.edu/tag/02FQ).
Proof: Use `Torsor.FreeExtension`, the sheaf pushout imposing
`[y] - [x] = T.sub x y` on the free abelian sheaf of torsor sections.
Its degree projection and coefficient inclusion form a short exact sequence by
`Torsor.FreeExtension.shortExact`. Sheafification naturality makes the generator
map `t ↦ [t]` natural. The augmentation sends `[t]` to one, so the map takes values
in the lifting torsor of the global section one. Applying the pushout relation to
`(t, g +ᵥ t)` gives `[g +ᵥ t] = [t] + ι(g)`, proving equivariance. The proved theorem
`Torsor.Iso.ofHom` turns any equivariant map between torsors into an isomorphism:
simple transitivity gives injectivity, and local nonemptiness gives local
surjectivity; the sheaf property then gives the isomorphism. All constructions
have coefficient universe `u`, with no choice of an unproved existence witness.
(blueprint: lem-sc-zariski-torsor-representative-exists) -/
theorem zariski_torsor_representative_exists (X : Scheme.{u})
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (T : G.Torsor) :
    ∃ (E : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ι : G ⟶ E) (p : E ⟶
        (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u, 0} ℤ)))
      (hzero : ι ≫ p = 0)
      (hS : (ShortComplex.mk ι p hzero).ShortExact),
      Nonempty (Torsor.Iso T
        (Torsor.lifts (IsTerminal.ofUnique (⊤ : Opens X)) hS
          ((toSheafify (Opens.grothendieckTopology X)
            ((Functor.const (Opens X)ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u, 0} ℤ)))).app (op ⊤) ⟨1⟩))) := by
  let E := Torsor.FreeExtension.extension X T
  let ι := Torsor.FreeExtension.inclusion X T
  let p := Torsor.FreeExtension.projection X T
  have hz : ι ≫ p = 0 := Torsor.FreeExtension.inclusion_projection X T
  have hS : (ShortComplex.mk ι p hz).ShortExact := Torsor.FreeExtension.shortExact X T
  let htop := IsTerminal.ofUnique (⊤ : Opens X)
  let one := (toSheafify (Opens.grothendieckTopology X)
    (Torsor.FreeExtension.integers X)).app (op ⊤) ⟨1⟩
  refine ⟨E, ι, p, hz, hS, ⟨Torsor.Iso.ofHom (ObjectProperty.homMk
    { app U := TypeCat.ofHom fun t ↦ ⟨Torsor.FreeExtension.generator X T U t, ?_⟩
      naturality U V f := ?_ }) (fun U g t ↦ ?_)⟩⟩
  · change p.hom.app U (Torsor.FreeExtension.generator X T U t) =
      (sheafify (Opens.grothendieckTopology X)
        (Torsor.FreeExtension.integers X)).map (htop.from U.unop).op one
    rw [free_generator_degree]
    exact (congr_arg (fun η ↦ η (⟨1⟩ : ULift.{u, 0} ℤ))
      ((toSheafify (Opens.grothendieckTopology X)
        (Torsor.FreeExtension.integers X)).naturality (htop.from U.unop).op))
  · ext t
    apply Subtype.ext
    exact (free_generator_naturality X T f t).symm
  · apply Subtype.ext
    exact free_generator_vadd X T U g t

end CategoryTheory.Sheaf
