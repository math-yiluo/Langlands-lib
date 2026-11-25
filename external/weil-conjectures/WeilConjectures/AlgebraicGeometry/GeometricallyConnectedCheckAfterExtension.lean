/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.FieldTheory.CommonExtensionFields

/-!
# Geometric connectedness after a field extension

Source: Stacks Project, `varieties.tex`, Lemma 33.7.3, tag 054N
(blueprint: lem-weil-geometrically-connected-check-after-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Geometric connectedness over a field is equivalent to geometric connectedness
of its base change along any field extension.

Source: Stacks Project, `varieties.tex`, Lemma 33.7.3, tag 054N
(blueprint: lem-weil-geometrically-connected-check-after-extension).
Proof: If `X` is geometrically connected, every field extension of `k` gives a
connected base change, and this applies to extensions of `k'` by associativity
of base change. Conversely, for an arbitrary extension `k''/k`, choose a common
extension of `k'` and `k''` over `k`; geometric connectedness after `k'` makes
the common base change connected. The map from the common base change to the
`k''`-base change is a surjective base change, so connectedness descends along
its continuous surjective map. Pullback pasting and cancellation implement
the iterated base-change identifications directly; the common extension is
`Field.exists_common_extension`, and surjectivity of the projection is Mathlib's
base-change stability instance for `Surjective`.
(blueprint: lem-weil-geometrically-connected-check-after-extension). -/
theorem geometricallyConnected_iff_of_fieldExtension
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    GeometricallyConnected (X ↘ Spec (.of k)) ↔
      GeometricallyConnected
        (pullback.snd (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))):
            pullback (X ↘ Spec (.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ⟶
              Spec (.of k')) := by
  constructor
  · intro h
    infer_instance
  · intro h
    refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
    intro K _ _
    obtain ⟨M, _, _, i, j, _, _⟩ := Field.exists_common_extension k k' K
    let f := X ↘ Spec (.of k)
    let g := Spec.map (CommRingCat.ofHom (algebraMap k k'))
    let t := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let a := Spec.map (CommRingCat.ofHom i.toRingHom)
    let b := Spec.map (CommRingCat.ofHom j.toRingHom)
    have hab : a ≫ g = b ≫ t := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (i.commutes x).trans (j.commutes x).symm
    let p := pullback.fst (pullback.snd f t) b
    let q := pullback.snd (pullback.snd f t) b
    let r : pullback (pullback.snd f t) b ⟶ pullback f g :=
      pullback.lift (p ≫ pullback.fst f t) (q ≫ a) (by
        calc
          (p ≫ pullback.fst f t) ≫ f = (p ≫ pullback.snd f t) ≫ t := by
            rw [Category.assoc, pullback.condition, ← Category.assoc]
          _ = (q ≫ b) ≫ t := by rw [show p ≫ pullback.snd f t = q ≫ b from
            pullback.condition]
          _ = (q ≫ a) ≫ g := by simp only [Category.assoc, hab])
    have outer : IsPullback (p ≫ pullback.fst f t) q f (a ≫ g) := by
      rw [hab]
      exact (IsPullback.of_hasPullback (pullback.snd f t) b).flip.paste_vert
        (IsPullback.of_hasPullback f t).flip |>.flip
    have top : IsPullback r q (pullback.snd f g) a := by
      apply IsPullback.flip
      apply IsPullback.of_bot (t := (IsPullback.of_hasPullback f g).flip)
      · simpa [r] using outer.flip
      · simp [r]
    have : ConnectedSpace ↥(pullback (pullback.snd f t) b) :=
      GeometricallyConnected.geometrically_connectedSpace (f := pullback.snd f g)
        a r q top
    have : Surjective b := ⟨fun y ↦ ⟨default, Subsingleton.elim _ _⟩⟩
    exact p.surjective.connectedSpace p.continuous

end AlgebraicGeometry
