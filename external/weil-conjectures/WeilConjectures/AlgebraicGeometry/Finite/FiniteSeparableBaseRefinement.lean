/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# Refining a smooth projective base through a finite separable extension

Source: Stacks Project, Tags 0G80, 0C4Q, 087S, 01W9 and 01WC
(blueprint: lem-weil-pbc-finite-separable-base-refinement).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism to a finite separable extension is smooth, H-projective and proper if its
composite to the original field is smooth and H-projective.
Source: Stacks Project, Tags 0G80, 0C4Q, 087S, 01W9 and 01WC
(blueprint: lem-weil-pbc-finite-separable-base-refinement).

Proof:
1. Set `a : Spec L ⟶ Spec k` to be induced by the algebra map and `f = q ≫ a`.
   The map `a` is etale by lem-weil-pbc-finite-separable-extension-etale and separated by
   lem-weil-pbc-affine-source-morphism-separated.
2. Form `W = Z ×[Spec k] Spec L` (def-pc-fibre-product). Its projection `r` to `Z` is
   etale by lem-weil-pbc-etale-scheme-base-change. The graph `(id, q)` is a section of `r`,
   hence an open immersion by lem-weil-pbc-etale-section-clopen-immersion; only this
   clause of the section lemma is needed.
3. The projection `b : W ⟶ Spec L` is smooth by lem-pc-proper-base-change, clause (2).
   Composing with the graph gives smoothness of `q` by
   lem-pc-open-immersion-smooth-composition.
4. Choose an embedding of `Z` into projective space over `Spec k` with a finite type of
   homogeneous coordinates, witnessing def-kun-projective. By
   lemma-nagata-projective-space-base-change-pullback, its graph with `q` maps into
   projective space over `Spec L` with the same coordinate type.
5. The projection from that space to projective space over `Spec k` is separated by
   lem-weil-pbc-separated-base-change. Its composite with the graph is the original
   closed immersion. By lem-weil-pbc-closed-immersion-cancellation the graph is a
   closed immersion too, proving H-projectivity of `q` by def-kun-projective.
6. Apply the already proved upstream instance `IsHProjective.isProper`
   (lem-pc-projective-proper) to obtain properness of `q`. -/
theorem smooth_hProjective_proper_of_finite_separable_base
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (Z : Scheme.{u}) (q : Z ⟶ Spec (.of L))
    [Smooth (q ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)))]
    [IsHProjective (q ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)))] :
    Smooth q ∧ IsHProjective q ∧ IsProper q := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have : Etale a := by
    dsimp [a]
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr Algebra.Etale.of_finite_of_isSeparable
  let γ : Z ⟶ Limits.pullback (q ≫ a) a := Limits.pullback.lift (𝟙 Z) q (by simp)
  have hγ : γ ≫ Limits.pullback.fst (q ≫ a) a = 𝟙 Z := Limits.pullback.lift_fst _ _ _
  have : Mono γ := mono_of_mono_fac hγ
  have : Etale (γ ≫ Limits.pullback.fst (q ≫ a) a) := by
    rw [hγ]
    infer_instance
  have : Etale γ := Etale.of_comp γ (Limits.pullback.fst (q ≫ a) a)
  have : IsOpenImmersion γ := IsOpenImmersion.of_flat_of_mono γ
  have hq : γ ≫ Limits.pullback.snd (q ≫ a) a = q := Limits.pullback.lift_snd _ _ _
  have : Smooth q := by
    rw [← hq]
    infer_instance
  have : IsHProjective q := by
    obtain ⟨n, hn, i, hi, hf⟩ :=
      IsHProjective.exists_isClosedImmersion (f := q ≫ a)
    let j := ProjectiveSpace.liftBaseChange q i hf.symm
    refine ⟨n, hn, j, ?_, ?_⟩
    · dsimp [j]
      infer_instance
    · exact ProjectiveSpace.liftBaseChange_over q i hf.symm
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
