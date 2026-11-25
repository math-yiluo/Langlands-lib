/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatTargetLocus
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Flatness near a point from a flat test

This module proves only the descent step, after flatness of the test pullback
has been established. In the normalization application, the rational generic
section point is essential to establish that flatness: it is the hypothesis
`hZ` of `GaloisCover.stalk_normalization_depth_two_section_flat` and
`GaloisCover.exists_stalk_normalization_split_formal_test`.
Depth two alone does not establish the flat-pullback hypothesis here.

## References

* Stacks Project, Tag 0EYJ, flatness descent and openness
* Stacks Project, Tag 0EYJ, final flatness descent and neighbourhood argument
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace AlgebraicGeometry.Scheme

/-- A finite morphism is flat over a neighbourhood of x if a flat test through x
makes its pullback flat. This isolates descent and openness from the formal
splitting calculation. The assumption `Flat (pullback.snd p t)` is an input,
not a consequence of depth two. For the normalization application, the rational
point over the generic section is used upstream to split this pullback. -/
theorem stalk_normalization_depth_two_section_flat_core
    {L E T : Scheme.{u}} [IsLocallyNoetherian L]
    (p : E ⟶ L) [IsFinite p] (t : T ⟶ L)
    [Flat t] [Flat (pullback.snd p t)] (x : L) (b : T) (hb : t b = x) :
    ∃ W : L.Opens, x ∈ W ∧ Flat (p ∣_ W) := by
  -- The caller supplies pullback flatness; hb then lifts every point of the fibre.
  -- Descend flatness along the faithfully flat projection stalk map.
  let F : Set L := {y | ∀ z, p z = y → (p.stalkMap z).hom.Flat}
  let W : L.Opens := ⟨F, isOpen_setOf_finite_flat_stalks p⟩
  refine ⟨W, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, _⟩ :=
      Pullback.exists_preimage_pullback (f := p) (g := t) z b (hz.trans hb.symm)
    let g := Limits.pullback.fst p t
    have hcomp : ((g ≫ p).stalkMap w).hom.Flat := by
      rw [Limits.pullback.condition, Hom.stalkMap_comp, CommRingCat.hom_comp]
      exact (Flat.stalkMap t _).comp (Flat.stalkMap (Limits.pullback.snd p t) w)
    rw [Hom.stalkMap_comp, CommRingCat.hom_comp] at hcomp
    -- The projection g is a base change of the flat test t.
    -- Its stalk map is local, so its flatness is faithful flatness.
    have hg : (g.stalkMap w).hom.FaithfullyFlat := by
      algebraize [(g.stalkMap w).hom]
      have : Module.Flat _ _ := Flat.stalkMap g w
      have : IsLocalHom (algebraMap (E.presheaf.stalk (g w))
          ((Limits.pullback p t).presheaf.stalk w)) :=
        inferInstanceAs (IsLocalHom (g.stalkMap w).hom)
      exact Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hp : (p.stalkMap (g w)).hom.Flat := by
      algebraize [(p.stalkMap (g w)).hom, (g.stalkMap w).hom,
        (g.stalkMap w).hom.comp (p.stalkMap (g w)).hom]
      have : Module.Flat (L.presheaf.stalk (p (g w)))
          ((pullback p t).presheaf.stalk w) := hcomp
      have : Module.FaithfullyFlat (E.presheaf.stalk (g w))
          ((pullback p t).presheaf.stalk w) := hg
      exact Module.Flat.of_flat_of_faithfullyFlat
        (A := L.presheaf.stalk (p (g w))) (B := E.presheaf.stalk (g w))
        (C := (pullback p t).presheaf.stalk w)
    change g w = z at hw
    rwa [hw] at hp
  · apply Flat.of_stalkMap
    intro z
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap p W z)).mpr (z.2 z.1 rfl)

end AlgebraicGeometry.Scheme
