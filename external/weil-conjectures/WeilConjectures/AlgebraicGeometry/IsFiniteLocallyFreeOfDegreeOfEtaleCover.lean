/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent

/-!
# Descent of finite local freeness of fixed degree along an étale covering

Source: Stacks Project, Descent, Lemma 02VO, and Topologies, Lemma 022C
(blueprint: lem-weil-pbc-finite-locally-free-degree-etale-descent).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- Finite local freeness of degree `d` descends along a jointly surjective étale family.
Source: Stacks Project, Descent, Lemma 02VO, using Topologies, Lemma 022C
(blueprint: lem-weil-pbc-finite-locally-free-degree-etale-descent).

Proof:
1. The family is an fpqc covering (`def-weil-pbc-fpqc-covering`). Each member is flat
   (`def-weil-etale-morphism`). For an affine open of the target, cover its inverse images
   by affine opens (`def-pc-scheme`). Their images are open
   (`lem-weil-pbc-etale-morphism-open-map`), cover that affine open by joint surjectivity,
   and admit a finite subcover (`lem-weil-pbc-affine-scheme-qcqs`). This is the proof of 022C.
2. Each second projection (`def-pc-fibre-product`) is finite by the hypothesis
   (`def-pc-finite-locally-free`). Thus `h` is finite by
   `lem-weil-pbc-fpqc-descend-finite` applied to the fpqc covering from step 1.
3. Each second projection is flat, so `h` is flat by `lem-weil-pbc-fpqc-descend-flat`.
4. Each second projection is locally of finite presentation, so `h` is locally of finite
   presentation by `lem-weil-pbc-fpqc-descend-locally-finite-presentation`. With steps 2 and 3
   this gives finite local freeness (`def-pc-finite-locally-free`).
5. For any target point `t`, its fibre over its residue field (`def-weil-residue-field`,
   `def-pc-scheme-fibre`) is finite by `lem-weil-pbc-finite-morphism-permanence`. Let its
   degree be `e` (`def-weil-pbc-fibre-degree-bound`). Choose a point over `t` in a member
   of the cover. By `lem-weil-pbc-fibre-degree-base-change` the corresponding fibre of the
   second projection has the same degree `e`; its degree is `d` by hypothesis. Hence `e = d`
   at every target point, as required by `def-pc-finite-locally-free`. -/
theorem isFiniteLocallyFreeOfDegree_of_etale_cover
    {Y T : Scheme.{u}} (h : Y ⟶ T) (d : ℕ) {I : Type w}
    (T' : I → Scheme.{u}) (φ : ∀ i : I, T' i ⟶ T)
    (hφ : ∀ i : I, Etale (φ i))
    (hcover : ∀ t : T, ∃ (i : I) (t' : T' i), φ i t' = t)
    (hdegree : ∀ i : I, (pullback.snd h (φ i)).IsFiniteLocallyFreeOfDegree d) :
    h.IsFiniteLocallyFreeOfDegree d := by
  let (i : I) : Etale (φ i) := hφ i
  let (i : I) : (pullback.snd h (φ i)).IsFiniteLocallyFreeOfDegree d := hdegree i
  have hfpqc : Presieve.ofArrows T' φ ∈ Scheme.fpqcPrecoverage T := by
    apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨hcover, fun i ↦ ⟨inferInstance, inferInstance⟩⟩
  let : IsFinite h := isFinite_of_fpqc_cover h T' φ hfpqc (fun i ↦ inferInstance)
  let : Flat h := flat_of_fpqc_cover h T' φ hfpqc (fun i ↦ inferInstance)
  let : LocallyOfFinitePresentation h :=
    locallyOfFinitePresentation_of_fpqc_cover h T' φ hfpqc (fun i ↦ inferInstance)
  refine { fiberDegree_eq := ?_ }
  intro t
  obtain ⟨i, t', rfl⟩ := hcover t
  rw [← h.fiberDegree_of_isPullback (IsPullback.of_hasPullback h (φ i)) t']
  exact IsFiniteLocallyFreeOfDegree.fiberDegree_eq t'

end AlgebraicGeometry.Scheme.Hom
