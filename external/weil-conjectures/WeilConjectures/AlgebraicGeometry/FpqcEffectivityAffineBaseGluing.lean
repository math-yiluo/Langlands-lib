/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FpqcCanonicalPullbackDatum
import WeilConjectures.AlgebraicGeometry.FpqcEffectivityOpenLocal

/-! Auxiliary step of effective fpqc descent, following the Stacks Project. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Effectivity over all affine bases implies effectivity over arbitrary bases
for a class stable under the chosen pullbacks.
Source: Stacks Project, Descent, Tag 02W3, final general-base part of the proof.
(blueprint: lem-galois-fpqc-effectivity-affine-base-gluing)

For each affine open A of S, base change f and D to A. Base-change stability of
fpqc covers and hbase preserve the hypotheses, and hlocal gives an effective
object W_A over A. For nested affine opens B ⊆ A, the two objects over B have
canonically isomorphic pullbacks to X_B. Full faithfulness of fpqc descent of
morphisms gives a unique comparison isomorphism. Uniqueness proves the identity
and composition laws. These comparisons exhibit pullback squares, so relative
gluing over the directed affine cover constructs W over S. The local
identifications of W ×_S X with V agree on overlaps by the same uniqueness and
glue to an isomorphism; transport compatibility is checked on that open cover.
Its projection to W witnesses effectivity. No finite-coproduct or affine-source
hypothesis is used here, and empty bases give empty gluing. -/
theorem fpqc_effectivity_of_affine_bases (P : MorphismProperty Scheme.{u})
    (hbase : ∀ {Y V V' : Scheme.{u}} (g : Y ⟶ V) (h : V' ⟶ V),
      P g → P (pullback.snd g h))
    (hlocal : ∀ {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S),
      Presieve.singleton f ∈ Scheme.fpqcPrecoverage S →
      ∀ {V : Over X} (D : Over.DescentDatum f V), P V.hom → D.IsEffective)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {V : Over X} (D : Over.DescentDatum f V) (hV : P V.hom) : D.IsEffective := by
  apply fpqc_isEffective_of_affine_open_restrictions f hf D
  intro U
  let i := U.1.ι
  let h := pullback.fst f i
  let g := pullback.snd f i
  obtain ⟨E, hE⟩ := exists_canonical_pullback_descent_datum f (g ≫ i) h
    (pullback.condition (f := f) (g := i)) D
  let E' : Over.DescentDatum g (Over.mk (pullback.snd V.hom h)) :=
    { transport := fun a b hab ↦ E.transport a b (by rw [← Category.assoc,
        ← Category.assoc, hab])
      transport_homMk_comp := by
        intro T T' k a b hab x
        exact E.transport_homMk_comp k a b _ x
      transport_self := E.transport_self
      transport_transport := by
        intro T a b c hab hbc x
        exact E.transport_transport a b c _ _ x }
  have hg : Presieve.singleton g ∈ Scheme.fpqcPrecoverage (U : Scheme.{u}) := by
    rw [← Presieve.ofArrows_pUnit.{0}] at hf ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} ↦ f) hf i
      (fun _ ↦ g) (fun _ ↦ h) (fun _ ↦ (IsPullback.of_hasPullback f i).flip)
  have hP : P (pullback.snd V.hom h) := hbase V.hom h hV
  refine ⟨E', hlocal g hg E' hP, ?_⟩
  intro T a b hab x
  exact hE a b (by rw [← Category.assoc, ← Category.assoc, hab]) x

end AlgebraicGeometry
