/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent

/-!
# Base change and étale descent of closed proper supports

Source: Stacks Project, Tags 0CYP and 0F4J
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Closed subsets proper over the base remain proper after any base change, and
properness descends along any jointly surjective étale family. No quasi-compactness
of the ambient morphism, base, or covering members is assumed.
Source: Stacks Project, Tags 0CYP and 0F4J.
(auxiliary; not a blueprint node)

Proof:
1. Give `C` its reduced induced closed structure with immersion `i`. Pull `i` back
   along `T ×[S] S' → T`. The range formula `Scheme.Pullback.range_snd` identifies
   the resulting closed immersion's image with the inverse image of `C`.
2. Paste this pullback square with the square defining `T ×[S] S'`. Properness is
   stable under this base change. Independence of the chosen closed structure
   (`closed_subset_proper_over_base_properties`) proves the first clause.
3. Regard the jointly surjective étale family as a cover of the identity object in
   the small étale site and apply `fpqcCover_of_smallEtaleCover`. By independence
   of closed structure, each pulled-back closed subscheme from step 1 is proper.
4. The pasted squares identify these morphisms with the canonical base changes of
   `i ≫ p`. Transport properness across their canonical isomorphisms and apply
   `isProper_of_fpqc_cover`. This is precisely properness of `C` over `S`.
-/
theorem closed_proper_support_locality
    {T S : Scheme.{u}} (p : T ⟶ S) [LocallyOfFiniteType p]
    (C : TopologicalSpace.Closeds T) :
    (∀ (S' : Scheme.{u}) (w : S' ⟶ S), IsClosedSubsetProperOver p C →
      IsClosedSubsetProperOver (pullback.snd p w)
        (C.preimage (pullback.fst p w).continuous)) ∧
    (∀ (I : Type v) (Sᵢ : I → Scheme.{u}) (w : ∀ i, Sᵢ i ⟶ S)
      [∀ i, Etale (w i)],
      (∀ s : S, ∃ (i : I) (x : Sᵢ i), w i x = s) →
      (∀ i, IsClosedSubsetProperOver (pullback.snd p (w i))
        (C.preimage (pullback.fst p (w i)).continuous)) →
      IsClosedSubsetProperOver p C) := by
  classical
  let i := (IdealSheafData.vanishingIdeal C).subschemeι
  have hi : Set.range i = (C : Set T) := by simp [i]
  have hrange (S' : Scheme.{u}) (w : S' ⟶ S) :
      Set.range (pullback.snd i (pullback.fst p w)).base =
        (C.preimage (pullback.fst p w).continuous : Set (pullback p w : Scheme.{u})) := by
    change Set.range (pullback.snd i (pullback.fst p w)) =
      (pullback.fst p w) ⁻¹' (C : Set T)
    rw [Scheme.Pullback.range_snd, hi]
  constructor
  · intro S' w hp
    have : IsProper (i ≫ p) := hp
    have hsq := (IsPullback.of_hasPullback i (pullback.fst p w)).paste_vert
      (IsPullback.of_hasPullback p w)
    have hp' : IsProper (pullback.snd i (pullback.fst p w) ≫ pullback.snd p w) :=
      MorphismProperty.of_isPullback hsq inferInstance
    apply (closed_subset_proper_over_base_properties (pullback.snd p w)
      (C.preimage (pullback.fst p w).continuous)).1.mpr
    exact ⟨_, pullback.snd i (pullback.fst p w), inferInstance, hrange S' w, hp'⟩
  · intro I Sᵢ w _ hsurj hp
    let U : S.Etale := Etale.mk (𝟙 S)
    let V : I → S.Etale := fun a ↦ Etale.mk (w a)
    let e : ∀ a, V a ⟶ U := fun a ↦
      MorphismProperty.Over.homMk (w a) (Category.comp_id _)
    have hcover : Sieve.ofArrows V e ∈ S.smallEtaleTopology U := by
      apply (ofArrows_mem_smallEtaleTopology_iff e).mpr
      apply Set.eq_univ_of_forall
      intro s
      obtain ⟨a, x, hx⟩ := hsurj s
      exact Set.mem_iUnion.mpr ⟨a, x, hx⟩
    have hfpqc : Presieve.ofArrows Sᵢ w ∈ fpqcPrecoverage S :=
      fpqcCover_of_smallEtaleCover e hcover
    change IsProper (i ≫ p)
    apply isProper_of_fpqc_cover (i ≫ p) Sᵢ w hfpqc
    intro a
    have hp' : IsProper
        (pullback.snd i (pullback.fst p (w a)) ≫ pullback.snd p (w a)) :=
      (closed_subset_proper_over_base_properties (pullback.snd p (w a))
        (C.preimage (pullback.fst p (w a)).continuous)).2.1.mp (hp a) _ _
          (hrange (Sᵢ a) (w a))
    have hsq := (IsPullback.of_hasPullback i (pullback.fst p (w a))).paste_vert
      (IsPullback.of_hasPullback p (w a))
    rw [← hsq.isoPullback_inv_snd]
    infer_instance

end AlgebraicGeometry.Scheme
