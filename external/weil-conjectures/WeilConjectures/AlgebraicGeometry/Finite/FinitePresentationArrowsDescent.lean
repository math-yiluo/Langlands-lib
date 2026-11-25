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
# Common-stage descent of finitely many arrows between specified models

Source: Stacks Project, Limits, Tag 01ZM, clause (2).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Finitely many arrows between specified finite-presentation models descend to one stage.
Different arrows may have different sources and targets. The equations retain their original
limit arrows, rather than only their isomorphism classes.

Source: Stacks Project, Limits, Tag 01ZM, clause (2), with common refinement.
(blueprint: lem-weil-pbc-finite-presentation-arrows-descent)

Proof: Descend each arrow by 01ZM(2). Choose a common lower bound of their finitely many
stages. Pullback maps from this common stage to each arrow's stage precompose the descended
arrows. Their equations over the base and compatibility at the limit follow by pullback
projection identities and cone naturality. Empty arrow families are permitted.
-/
theorem exists_finitePresentation_arrows_stage
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {κ : Type v} [Finite κ] (V W : κ → Scheme.{u})
    (pV : ∀ a, V a ⟶ D.obj i) (pW : ∀ a, W a ⟶ D.obj i)
    [∀ a, LocallyOfFinitePresentation (pV a)] [∀ a, QuasiCompact (pV a)]
    [∀ a, QuasiSeparated (pV a)]
    [∀ a, LocallyOfFinitePresentation (pW a)] [∀ a, QuasiCompact (pW a)]
    [∀ a, QuasiSeparated (pW a)]
    (ψ : ∀ a, pullback (pV a) (c.π.app i) ⟶ W a)
    (hψ : ∀ a, ψ a ≫ pW a = pullback.fst (pV a) (c.π.app i) ≫ pV a) :
    ∃ (j : I) (f : j ⟶ i) (θ : ∀ a, pullback (pV a) (D.map f) ⟶ W a),
      (∀ a, θ a ≫ pW a = pullback.fst (pV a) (D.map f) ≫ pV a) ∧
      ∀ a, pullback.map (pV a) (c.π.app i) (pV a) (D.map f)
        (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) ≫ θ a = ψ a := by
  classical
  have hex (a : κ) := Scheme.exists_pullback_hom_of_isLimit hc (pV a) (pW a) (ψ a) (hψ a)
  choose k b θ hθ heq using hex
  obtain ⟨j, f, m, hm⟩ := IsCofiltered.wideCospan b
  let M (a : κ) := pullback.map (pV a) (D.map f) (pV a) (D.map (b a))
    (𝟙 _) (D.map (m a)) (𝟙 _) (by simp) (by
      rw [Category.comp_id, ← D.map_comp]
      exact congrArg D.map (hm a).symm)
  refine ⟨j, f, fun a ↦ M a ≫ θ a, ?_, ?_⟩
  · intro a
    simp [M, hθ a]
  · intro a
    have hm : pullback.map (pV a) (c.π.app i) (pV a) (D.map f)
        (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) ≫ M a =
        pullback.map (pV a) (c.π.app i) (pV a) (D.map (b a))
          (𝟙 _) (c.π.app (k a)) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext <;> simp [M, c.w (m a)]
    rw [← Category.assoc, hm]
    exact heq a

end AlgebraicGeometry
