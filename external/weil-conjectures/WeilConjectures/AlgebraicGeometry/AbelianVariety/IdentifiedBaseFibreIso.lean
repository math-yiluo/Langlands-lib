/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-! Pullback pasting over identified bases.

(blueprint: new-identified-base-fibre-iso)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Identify an iterated pullback with a fibre product over an isomorphic base.
Source: Stacks Project, Tag 01JP, fibre products and base change.
(blueprint: new-identified-base-fibre-iso)

Proof: First paste the two pullback squares. Then apply the pullback map induced
by the identity of X and the given base isomorphism r. The induced pullback map
is an isomorphism. The first projection follows from the two pullback projection
identities. The second projection follows from the same identities and cancellation
of r followed by its inverse. The argument includes empty fibre products. -/
theorem identifiedBaseFibreIso
    {X S W T T' : Scheme.{v}} (f : X ⟶ S) (k : W ⟶ S)
    (g : T ⟶ W) (t : T' ⟶ S) (r : T ≅ T') (h : g ≫ k = r.hom ≫ t) :
    ∃ e : pullback (pullback.snd f k) g ≅ pullback f t,
      e.hom ≫ pullback.fst f t =
        pullback.fst (pullback.snd f k) g ≫ pullback.fst f k ∧
      e.hom ≫ pullback.snd f t ≫ r.inv = pullback.snd (pullback.snd f k) g := by
  classical
  let d := pullback.map f (g ≫ k) f t (𝟙 X) r.hom (𝟙 S)
    (by simp) (by simpa using h)
  have : IsIso d := by dsimp only [d]; infer_instance
  let e := pullbackLeftPullbackSndIso f k g ≪≫ asIso d
  refine ⟨e, ?_, ?_⟩
  · simp [e, d]
  · simp [e, d]

end AlgebraicGeometry.Scheme
