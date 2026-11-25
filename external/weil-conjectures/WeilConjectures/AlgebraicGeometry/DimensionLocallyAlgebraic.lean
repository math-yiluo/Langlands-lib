/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Dimension of an irreducible locally algebraic scheme

Source: Stacks Project, Varieties, Lemma 33.20.3, Tag 0A21, part (3)
(blueprint: lem-sc-dimension-locally-algebraic).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For an irreducible scheme locally of finite type over a field, every nonempty open subset
and every point have the dimension of the whole scheme. Source: Stacks Project, Varieties,
Lemma 33.20.3, Tag 0A21, part (3) (blueprint: lem-sc-dimension-locally-algebraic).

Proof:
1. Replace `X` by its reduction (`def-weil-pbc-scheme-reduction`). The reduction map is a closed
   immersion and a homeomorphism (`lem-weil-pbc-reduction-universal-homeomorphism`), so its
   source is reduced and irreducible, hence integral (`def-pc-integral-scheme`). The map is
   locally of finite type (`lem-weil-pbc-immersion-base-change-lft`), and composition preserves
   that property (`lem-weil-pbc-proper-fp-permanence`). All the dimensions in the statement
   are preserved by the homeomorphism (`lem-weil-pbc-homeomorphism-krull-dimension`).
2. Choose a nonempty affine open `W₀` using `lem-weil-pbc-affine-opens-basis`, and put
   `d = dim W₀`. Every nonempty affine open has dimension `d` by
   `lem-sc-integral-locally-algebraic-affine-opens-dimension`: a closed point in the intersection
   compares their dimensions with its local-ring dimension (Stacks 0478 and 00OS).
3. A nonempty open `U` contains a nonempty affine open `W` by
   `lem-weil-pbc-affine-opens-basis`. Thus `d = dim W ≤ dim U` by
   `lem-weil-pbc-open-subspace-dimension-monotone`.
4. By `lem-weil-pbc-dimension-supremum-local-dimensions`, `dim U` is the supremum of its
   dimensions at points. Each point of `U` has an affine neighbourhood `W` contained in `U`,
   by `lem-weil-pbc-affine-opens-basis`. Its dimension at the point is at most `dim W = d`
   by `def-kun-topological-dimension-at-point`; the subspace topologies agree. Hence `dim U ≤ d`.
5. The preceding inequalities give `dim U = d`; applying this to `U = X` gives `dim X = d`,
   proving the first assertion.
6. Every open neighbourhood of a point `x` is nonempty and therefore has dimension `dim X`.
   The minimum of these dimensions is `dim X`, giving the second assertion by
   `def-kun-dimension`. -/
theorem dimension_locally_algebraic {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [IrreducibleSpace X] :
    (∀ U : X.Opens, (U : Set X).Nonempty →
      topologicalKrullDim (U : Set X) = topologicalKrullDim X) ∧
    (∀ x : X, topologicalKrullDimAt x = topologicalKrullDim X) := by
  have hred := reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism X
  let i := X.nilradical.subschemeι
  have hi : IsHomeomorph i :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isEmbedding, hred.2.2.1.1⟩
  let e := hi.homeomorph i
  have : IrreducibleSpace X.nilradical.subscheme := e.irreducibleSpace_iff.mpr inferInstance
  have : IsReduced X.nilradical.subscheme := hred.1
  have : IsIntegral X.nilradical.subscheme :=
    (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩
  have hdim : topologicalKrullDim X.nilradical.subscheme = topologicalKrullDim X :=
    hi.topologicalKrullDim_eq i
  have hopen (U : X.Opens) (hU : (U : Set X).Nonempty) :
      topologicalKrullDim (U : Set X) = topologicalKrullDim X := by
    let V : X.nilradical.subscheme.Opens := U.comap ⟨i, i.continuous⟩
    have : Nonempty V := by
      obtain ⟨x, hx⟩ := hU
      obtain ⟨y, hy⟩ := hi.surjective x
      exact ⟨⟨y, by change i y ∈ U; rw [hy]; exact hx⟩⟩
    have he : topologicalKrullDim (V : Set X.nilradical.subscheme) =
        topologicalKrullDim (U : Set X) :=
      (e.subtype (p := fun y ↦ y ∈ V) (q := fun x ↦ x ∈ U)
        (fun _ ↦ Iff.rfl)).isHomeomorph.topologicalKrullDim_eq _
    rw [← he, ← hdim]
    exact topologicalKrullDim_opens_eq (i ≫ (X ↘ Spec (.of k))) V
  refine ⟨hopen, fun x ↦ ?_⟩
  apply topologicalKrullDimAt_eq_of_forall
  intro U hx
  exact hopen U ⟨x, hx⟩

end AlgebraicGeometry
