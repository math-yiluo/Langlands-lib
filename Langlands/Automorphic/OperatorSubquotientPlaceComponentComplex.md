# Place components of irreducible operator subquotients at the complex places

Lean module: `Langlands.Automorphic.OperatorSubquotientPlaceComponentComplex`.
It imports `Langlands.Automorphic.OperatorSubquotientPlaceComponent` (the
real-place module of this proof, which supplies the descent helpers, the
commutation laws between real and complex places and the `gkSpan` lemmas)
and, through it, the place-component machinery
(`PlaceComponentExistence`, `PlaceComponentCarrierComplex`). It changes no
published file.

This module is part of the proof of
`Langlands.Automorphic.LocalComponentExistenceStatement`. It
proves the complex-place conjunct, apart from the final packaging done in
`LocalComponentExistenceProof`.

Notation as in `OperatorSubquotientPlaceComponent.md`, with `v` a complex
place: `κ_v = Q.complexPlaceCompactRepresentation v` (translation by `U(n)`
at `v`, `CK = Matrix.unitaryGroup (Fin n) ℂ`) and
`π_v = Q.complexPlaceLieAction v` (right differentiation by
`ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` at `v`).

## Main declarations

```lean
theorem OperatorSubquotient.isComplexGKModule_complexPlace (v : CP) :
    Archimedean.IsComplexGKModule n (Q.complexPlaceCompactRepresentation v)
      (Q.complexPlaceLieAction v)

theorem OperatorSubquotient.representation_mem_of_complexPlaceStable (v : CP)
    (Z : Submodule ℂ Q.Space) (hmap : …) (hκ : …) (hπ : …)
    (a : automorphicOperatorAlgebra F n) : ∀ x ∈ Z, Q.representation a x ∈ Z

theorem OperatorSubquotient.exists_complexPlace_detection (hQ : Q.IsIrreducible)
    [Nontrivial Q.Space] (v : CP) :
    ∃ (d : ℕ) (τ : CK →* Matrix (Fin d) (Fin d) ℂ), Continuous τ ∧
      ∀ W, IsStable κ_v π_v W → W ≠ ⊥ → intertwiners κ_v W d τ ≠ ⊥

theorem OperatorSubquotient.exists_complexPlaceComponent (hQ : Q.IsIrreducible)
    [Nontrivial Q.Space] (hJ : Q.IsJointlyAdmissible) (v : CP) :
    ∃ W : Submodule ℂ Q.Space,
      PlaceComponent.IsIrreducible κ_v π_v W ∧ PlaceComponent.IsAdmissible κ_v W

theorem OperatorSubquotient.isComplexPlaceIsotypic_restrict (hQ : Q.IsIrreducible)
    (v : CP) {W : Submodule ℂ Q.Space}
    (hW : PlaceComponent.IsIrreducible κ_v π_v W) :
    Q.IsComplexPlaceIsotypic v (restrictCompact hW.2.1) (restrictLie hW.2.1)
```

The hypotheses `hmap`, `hκ` and `hπ` are those of the real-place version
with `κ_v` and `π_v` the complex-place actions.

## Proofs

Each step is the complex-place copy of the corresponding step of
`OperatorSubquotientPlaceComponent.md`:

1. **`(𝔤, K)`-structure and commutation laws**
   (`isComplexGKModule_complexPlace`, `isLocallyFinite_complexPlace`,
   `isWeaklyContinuous_complexPlace`, `complexPlaceLieAction_comm_of_ne`,
   `complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne`,
   `complexPlaceCompactRepresentation_realPlaceLieAction`,
   `compact_comm_complexPlaceCompact`, `compact_comm_complexPlaceLie`,
   `compact_eq_complexPlace_mul`): descended from `Q.upper` through
   `Q.projection` with the helpers `forall_of_projection`,
   `comp_eq_of_projection`, `eq_comp_of_projection` and `dual_projection`.
2. **Operator stability** (`complexLieAction_mem_of_complexPlaceStable`,
   `envelopingAction_mem_of_complexPlaceStable`,
   `representation_mem_of_complexPlaceStable`,
   `eq_bot_or_eq_top_of_complexPlaceStable`): induction over the generators
   of the operator algebra; in the Lie algebra step the term at `v` of
   `complexify_action_eq_sum_place` preserves `Z` by hypothesis, and the
   terms at the real places and the other complex places commute with
   `κ_v` and `π_v` (the real-complex law is
   `realPlaceLieAction_comm_complexPlace` of the real-place module).
3. **Detection** (`exists_complexPlace_detection`): the free set of
   `exists_not_mem_freeSet` (`PlaceComponentDetection`) is stable, hence `⊥`.
4. **The carrier** (`complexCarrier`, `isStable_complexCarrier`,
   `lift_mem_jointMultiplicity_complex`, `isAdmissible_complexCarrier`): as
   in `PlaceComponentCarrierComplex`, with the condition `q.2 v = 1` on the
   compact factors; admissible by joint admissibility of `Q`.
5. **Existence** (`exists_complexPlaceComponent`): the argument of
   `PlaceComponentExistence.exists_complexPlaceComponent` with steps 3 and
   4.
6. **Isotypy** (`isComplexPlaceIsotypic_restrict`): the `gkSpan` from the
   restricted module of `W` is stable in the sense of step 2 (the `GKSpan`
   lemmas of the real-place module), hence `⊥` or `⊤`, and it is not `⊥`
   (`gkSpan_restrict_ne_bot`).

## Provenance and route

As for the real places (`OperatorSubquotientPlaceComponent.md`): a port of
the construction for cuspidal realizations to operator
subquotients, for the archimedean part of Getz–Hahn (2024), Lemma 6.3.6
and Theorem 6.3.7, p.165 (PDF 179), proof p.166 (PDF 180)
(`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`), with
the isotypy argument of Flath (1979), proof of Theorem 1, p.180 (PDF 176)
(`flath-1979-tensor-products`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`).

## Axioms

`lake build` reports only `propext`, `Classical.choice` and
`Quot.sound` for the final theorem
`Langlands.Automorphic.localComponentExistence`, which depends on this
module.
