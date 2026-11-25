/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# A common model for a finite family over an inverse limit

Source: Stacks Project, Limits, Tag 01ZM, object descent and common refinement.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Finitely many finitely presented objects over an affine-transition qcqs inverse limit
have models over a single common stage. The original objects, and not just their isomorphism
classes, occur in the displayed cartesian squares.

Source: Stacks Project, Limits, Tag 01ZM, clause (1), with a common refinement.
(blueprint: lem-weil-pbc-finite-presentation-family-descent)

Proof: Descend each object separately by 01ZM. Choose a common lower bound of the finitely
many stages and pull all the models back to it. Local finite presentation, quasi-compactness
and quasi-separatedness survive this base change. Pullback pasting gives the cartesian
squares for the original objects. For an empty family choose any stage of the cofiltered
system; the families of models and squares are empty.
-/
theorem exists_finitePresentation_family_stage
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    {κ : Type v} [Finite κ] (X : κ → Scheme.{u}) (p : ∀ a, X a ⟶ c.pt)
    [∀ a, LocallyOfFinitePresentation (p a)] [∀ a, QuasiCompact (p a)]
    [∀ a, QuasiSeparated (p a)] :
    ∃ (i : I) (Y : κ → Scheme.{u}) (q : ∀ a, Y a ⟶ D.obj i)
      (h : ∀ a, X a ⟶ Y a),
      (∀ a, LocallyOfFinitePresentation (q a)) ∧
      (∀ a, QuasiCompact (q a)) ∧ (∀ a, QuasiSeparated (q a)) ∧
      ∀ a, IsPullback (h a) (p a) (q a) (c.π.app i) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  have hex (a : κ) := Scheme.exists_isPullback_of_finitePresentation hc (p a)
  choose k Y q hfp hqc hqs h H using hex
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  let b (a : κ) : i ⟶ k a :=
    (hi (Finset.mem_image_of_mem k (Finset.mem_univ a))).some
  let Y' (a : κ) := pullback (q a) (D.map (b a))
  let q' (a : κ) : Y' a ⟶ D.obj i := pullback.snd (q a) (D.map (b a))
  refine ⟨i, Y', q', fun a ↦ isPullbackLift D c (b a) (H a), ?_, ?_, ?_, ?_⟩
  · intro a
    have := hfp a
    exact inferInstanceAs (LocallyOfFinitePresentation (pullback.snd (q a) (D.map (b a))))
  · intro a
    have := hqc a
    exact inferInstanceAs (QuasiCompact (pullback.snd (q a) (D.map (b a))))
  · intro a
    have := hqs a
    exact inferInstanceAs (QuasiSeparated (pullback.snd (q a) (D.map (b a))))
  · intro a
    exact isPullback_isPullbackLift (b a) (H a)

end AlgebraicGeometry
