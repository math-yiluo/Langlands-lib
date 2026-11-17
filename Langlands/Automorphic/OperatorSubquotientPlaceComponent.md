# Place components of irreducible operator subquotients at the real places

Original proof author: Worker 3657.
Submission preparation: Worker 833. Verification: Workers 833 and 835.

Lean module: `Langlands.Automorphic.OperatorSubquotientPlaceComponent`. It
imports `Langlands.Automorphic.PlaceComponentExistence` and
`Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction` (Worker
174's place-component machinery for cuspidal realizations) and
`Langlands.Automorphic.OperatorSubquotientLocalComponentStatement` (the target
statement and its isotypy predicates). It changes no published file.

This module is part of the proof of
`Langlands.Automorphic.LocalComponentExistenceStatement` (Task 6815). It
proves the real-place conjunct, apart from the final packaging done in
`LocalComponentExistenceProof`, and it contains the general `gkSpan` lemmas
that the complex-place module
`OperatorSubquotientPlaceComponentComplex` also uses.

Throughout, `Q : OperatorSubquotient F n` is an operator subquotient of
`GL_n` over a number field `F`, `Q.upper` is its numerator realization,
`Q.projection : Q.upper.Space → Q.Space` is the quotient map, and `v` is a
real place. `κ_v = Q.realPlaceCompactRepresentation v` (translation by
`O(n)` at `v`) and `π_v = Q.realPlaceLieAction v` (right differentiation by
`ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` at `v`) are the published place actions
(`OperatorSubquotientPlaceAction.lean`, `OperatorSubquotientLieAction.lean`).

## Main declarations

```lean
theorem OperatorSubquotient.isRealGKModule_realPlace (v : RP) :
    Archimedean.IsRealGKModule n (Q.realPlaceCompactRepresentation v)
      (Q.realPlaceLieAction v)

theorem OperatorSubquotient.representation_mem_of_realPlaceStable (v : RP)
    (Z : Submodule ℂ Q.Space)
    (hmap : ∀ A : Q.Space →ₗ[ℂ] Q.Space, (A commutes with κ_v) →
      (A commutes with π_v) → ∀ x ∈ Z, A x ∈ Z)
    (hκ : Z is κ_v-stable) (hπ : Z is π_v-stable)
    (a : automorphicOperatorAlgebra F n) : ∀ x ∈ Z, Q.representation a x ∈ Z

theorem OperatorSubquotient.exists_realPlace_detection (hQ : Q.IsIrreducible)
    [Nontrivial Q.Space] (v : RP) :
    ∃ (d : ℕ) (τ : RK →* Matrix (Fin d) (Fin d) ℂ), Continuous τ ∧
      ∀ W, IsStable κ_v π_v W → W ≠ ⊥ → intertwiners κ_v W d τ ≠ ⊥

theorem OperatorSubquotient.exists_realPlaceComponent (hQ : Q.IsIrreducible)
    [Nontrivial Q.Space] (hJ : Q.IsJointlyAdmissible) (v : RP) :
    ∃ W : Submodule ℂ Q.Space,
      PlaceComponent.IsIrreducible κ_v π_v W ∧ PlaceComponent.IsAdmissible κ_v W

theorem OperatorSubquotient.isRealPlaceIsotypic_restrict (hQ : Q.IsIrreducible)
    (v : RP) {W : Submodule ℂ Q.Space}
    (hW : PlaceComponent.IsIrreducible κ_v π_v W) :
    Q.IsRealPlaceIsotypic v (restrictCompact hW.2.1) (restrictLie hW.2.1)
```

Here `RP` is the type of real places and `RK = O(n)`
(`Matrix.unitaryGroup (Fin n) ℝ`). The statements above abbreviate the
commutation and stability hypotheses; the Lean statements spell them out.

## Proofs

1. **Descent from the numerator** (`forall_of_projection`,
   `comp_eq_of_projection`, `eq_comp_of_projection`, `dual_projection`).
   Every place action of `Q` is the descent of the corresponding action of
   `Q.upper` through `Q.projection`; the Library records this as the
   `*_projection` lemmas of `OperatorSubquotientPlaceAction.lean` and
   `OperatorSubquotientLieAction.lean`. Since `Q.projection` is surjective,
   an identity between composites of descended maps holds on `Q` once it
   holds for their lifts on `Q.upper`, and a linear functional `μ` on `Q`
   pulls back to the functional `μ ∘ Q.projection` on `Q.upper`.
2. **The `(𝔤, K)`-structure** (`isRealGKModule_realPlace`). The four axioms
   of `Archimedean.IsRealGKModule` for `Q.upper`
   (`OperatorRealization.isRealGKModule_realPlace`) descend: `K`-finiteness
   is the Library's `realPlaceCompactRepresentation_isFiniteVector`;
   continuity and the derivative formula are checked on `μ ∘ Q.projection`;
   the covariance law `k · X · k⁻¹` is an identity of composites (step 1).
   The commutation laws between the actions at `v` and at the other places
   (`realPlaceLieAction_comm_of_ne`, `realPlaceLieAction_comm_complexPlace`,
   `realPlaceCompactRepresentation_realPlaceLieAction_of_ne`,
   `realPlaceCompactRepresentation_complexPlaceLieAction`,
   `compact_comm_realPlaceCompact`, `compact_comm_realPlaceLie`) and the
   splitting `compact_eq_realPlace_mul` of a compact translation into its
   factor at `v` and the rest descend the same way from the realization
   versions in `PlaceComponentRealization` and `PlaceComponentCarrier`.
3. **Operator stability** (`complexLieAction_mem_of_realPlaceStable`,
   `envelopingAction_mem_of_realPlaceStable`,
   `representation_mem_of_realPlaceStable`,
   `eq_bot_or_eq_top_of_realPlaceStable`). Let `Z` be stable under `κ_v`,
   `π_v` and every linear map `A` commuting with `κ_v` and `π_v`. The proof
   runs `Algebra.adjoin_induction` over the generators of the operator
   algebra:
   - a finite adelic translation commutes with `κ_v` and `π_v`;
   - a compact translation `k` is `κ_v(k_v)` times a translation trivial at
     `v`, which commutes with `κ_v` and `π_v`;
   - an element `z ⊗ X` of the complexified global Lie algebra acts by `z`
     times the sum over all infinite places of the place Lie actions
     (Library `complexify_action_eq_sum_place`); the term at `v` preserves
     `Z` by hypothesis, the others commute with `κ_v` and `π_v`;
   - the enveloping algebra is generated by the Lie algebra
     (`Langlands.Algebra.LieCasimir.enveloping_adjoin_range`).
   Hence `Z` is a subrepresentation of `Q.representation`, so for
   irreducible `Q` it is `⊥` or `⊤`.
4. **Detection** (`isLocallyFinite_realPlace`,
   `isWeaklyContinuous_realPlace`, `exists_realPlace_detection`). For
   `x₀ ≠ 0`, Worker 174's `exists_not_mem_freeSet` gives a continuous
   matrix representation `τ` of `O(n)` whose free set does not contain
   `x₀`. The free set is stable as in step 3 (`freeSet_map`,
   `freeSet_compact`, `freeSet_lie`), hence `⊥` or `⊤`, hence `⊥`; then
   `intertwiners_ne_bot_of_freeSet_eq_bot` gives the conclusion.
5. **The carrier** (`realCarrier`, `isStable_realCarrier`,
   `lift_mem_jointMultiplicity`, `isAdmissible_realCarrier`). As in
   `PlaceComponentCarrier`, the carrier consists of the linear maps
   `ℂ^m → Q` with values fixed by an open `L ≤ GL_n(𝔸_f)` that intertwine a
   given representation `R` of the compact factors with the compact action
   on the factors trivial at `v`. It is stable under post-composition with
   `κ_v` and `π_v`. A `τ`-intertwiner into the carrier, uncurried along
   `TensorProduct.lift`, lies in the joint multiplicity space of `L` and
   `τ ⊗ R`, so joint admissibility of `Q` makes the carrier admissible.
6. **Existence** (`exists_realPlaceComponent`). Worker 174's proof of the
   cuspidal case (`PlaceComponentExistence.exists_realPlaceComponent`),
   with steps 4 and 5 in place of their realization versions: a nonzero
   `f₀` fixed by an open `U`, the finite-dimensional compact orbit span
   `E` of `f₀`, the inclusion of `E` in coordinates as a nonzero element
   of the carrier, a minimal irreducible admissible stable `N₀` inside the
   carrier (`exists_isIrreducible_isAdmissible`), and its image under
   evaluation at a basis vector (`isIrreducible_map`,
   `injOn_of_isIrreducible`, `isAdmissible_map`).
7. **The span of `(𝔤, K)`-maps** (section `GKSpan`: `gkSpan`,
   `apply_mem_gkSpan`, `map_mem_gkSpan`, `comm_mem_gkSpan`,
   `compact_mem_gkSpan`, `lie_mem_gkSpan`, `subtype_mem_gkHoms`,
   `gkSpan_restrict_ne_bot`). For general `(𝔤, K)`-actions on `V` and `W`,
   `gkSpan` is the span of the ranges of the maps in
   `Archimedean.gkHoms`. It is stable under the `K`- and `𝔤`-actions on `W`
   and under every linear map of `W` commuting with them, because composing
   a `(𝔤, K)`-map with such an operator gives a `(𝔤, K)`-map. For a nonzero
   stable subspace `Z` of `W`, the inclusion of `Z` is a `(𝔤, K)`-map from
   the restricted module, so the span is nonzero.
8. **Isotypy** (`isRealPlaceIsotypic_restrict`). For an irreducible
   place-stable `W`, the `gkSpan` from the restricted module of `W` to
   `(κ_v, π_v)` is stable in the sense of step 3 (step 7), hence `⊥` or
   `⊤`, and it is not `⊥`. It is therefore `⊤`, which is
   `Q.IsRealPlaceIsotypic v` by definition.

## Provenance and route

Steps 4–6 port Worker 174's construction for cuspidal realizations
(`PlaceComponentExistence`, `PlaceComponentRealization`,
`PlaceComponentCarrier`; Library) from `CuspidalOperatorRealization` to
`OperatorSubquotient`. Worker 174 proves the stability of the free set
separately for each kind of generator (`realFreeSet_finite`, …,
`realFreeSet_operator`); here one operator-stability theorem (step 3) serves
both the free set (detection) and `gkSpan` (isotypy).

The mathematics is the archimedean part of Getz–Hahn, *An introduction to
automorphic representations* (2024), Lemma 6.3.6 and Theorem 6.3.7, p.165
(PDF 179), with the proof of Theorem 6.3.7 on p.166 (PDF 180)
(`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`). The
isotypy argument of step 8 is the one in Flath, *Decomposition of
representations into tensor products* (1979), proof of Theorem 1, p.180
(PDF 176), which ends with "the restriction of `W` to `G_i` is
`W_i`-isotypic" (`flath-1979-tensor-products`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`). The
implemented proof uses neither Flath's theorem nor a tensor factorization:
irreducibility comes from the minimal-multiplicity argument, admissibility
from joint admissibility, and isotypy from the operator-stability theorem.

## Axioms

`lean_check` (lake build) of this module and of
`LocalComponentExistenceProof` reports only `propext`, `Classical.choice`
and `Quot.sound` for the final theorem
`Langlands.Automorphic.localComponentExistence`.
