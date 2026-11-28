# Trace compression for an isotypic Hilbert representation

The module `Langlands.Analysis.IsotypicTraceCompressionStatement` states the proposition
`Langlands.Analysis.OperatorIdeals.IsotypicTraceCompressionStatement`. It does not prove it.

## Statement

Let `G` be a group, and let `σ : G →* (H →L[ℂ] H)` and `π : G →* (E →L[ℂ] E)` act on complex
Hilbert spaces `H` and `E`. The hypotheses are:

* both actions preserve inner products. Each `σ g` has the inverse `σ g⁻¹`, so the actions are
  unitary;
* `σ` is topologically irreducible (`IsTopologicallyIrreducible`: `H` is nonzero and has no
  closed `σ`-invariant subspace other than `0` and `H`);
* the vectors `J x`, for `J` in `boundedIntertwiners σ π` (bounded `J : H → E` with
  `J (σ g x) = π g (J x)`) and `x : H`, span a dense subspace of `E`. Hence `π` is isotypic of
  type `σ`.

The conclusion asserts one bounded operator `Q` on `E` with two properties:

1. `Q` commutes with every bounded `Y` on `E` that commutes with all `π g`;
2. for all bounded `A` on `H` and `X` on `E` with `X (J x) = J (A x)` for every bounded
   intertwiner `J` and every `x : H`:
   * if `A = 0`, then `X = 0`;
   * if `Y` commutes with all `π g`, `A ≠ 0`, `A` is trace class and `X * Y` is trace class,
     then `Q * Y` is trace class and
     `operatorTrace (X * Y) = operatorTrace A * operatorTrace (Q * Y)`.

`Q` is chosen before `A`, `X` and `Y`. The Lean existential asks only for the commutation and
trace properties of `Q`. It does not say that `Q` is a projection, although the witness below is
one. Products of operators are compositions. `IsTraceClass` and `operatorTrace` are the
Library's trace-class predicate and chosen-basis trace on each of `H` and `E`. By
`Langlands.Analysis.OperatorIdeals.operatorTraceBasis`, on trace-class operators `operatorTrace`
equals the diagonal sum in every Hilbert basis. So the identity is basis-independent. The
definition has the universe parameters `uG`, `uH` and `uE` of `G`, `H` and `E`, and they vary
independently.

The hypothesis `A ≠ 0` matters. For `A = 0` we get `X = 0` and `X * Y = 0` for every `Y`, but
`Q * Y` need not be trace class. If `A ≠ 0` and `operatorTrace A = 0`, the conclusion still
says that `Q * Y` is trace class, and then `operatorTrace (X * Y) = 0`.

## Source and derivation

This proposition is derived from the multiplicity description of an isotypic unitary
representation. The cited results are from Folland, *A Course in Abstract Harmonic Analysis*,
second edition (2015), registered as `folland-2015-abstract-harmonic-analysis-second`, SHA-256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`:

* Theorem 3.5 (Schur's lemma), printed p. 77 (PDF p. 90). Part (a): a unitary representation
  is irreducible if and only if its commutant contains only scalars. The proof of part (b): the
  adjoint of an intertwiner intertwines in the reverse direction, so `T* T` lies in the
  commutant of the source.
* Theorem 7.11, printed pp. 234–235 (PDF pp. 247–248). If the only operators commuting with a
  set `S` of operators on `H₁` are scalars, then the operators on `H₁ ⊗ H₂` commuting with every
  `S ⊗ I` are exactly the operators `I ⊗ T`.
* The proof of Theorem 7.17, printed p. 237 (PDF p. 250). After a unitary transformation,
  that proof writes a primary representation of a type I group as `π₁ ⊗ I` on `H₁ ⊗ H₂`,
  with `π₁` irreducible. Then Schur's lemma and
  Theorem 7.11 write each operator in its commutant as `I ⊗ T`.

Folland works with strongly continuous unitary representations of locally compact groups on
nonzero Hilbert spaces (§3.1, printed p. 73, PDF p. 86). The arguments below use only the
algebraic intertwining relations, the adjoint and the spectral theorem through Schur's lemma.
So the proposition takes `G` to be an arbitrary group with no topology and puts no continuity
condition on the actions. It also allows `E = 0`.

The tensor decomposition is derived as follows. Let `M = boundedIntertwiners σ π`. For
`J, J' ∈ M`, the operator `J'* J` commutes with `σ`, so it is a scalar `⟨J', J⟩_M` times the
identity. For a unit vector `x₀` this scalar is `⟪J' x₀, J x₀⟫`. Since the commutant of `σ`
is scalar, `boundedIntertwinerEvaluationIsometry` in
`Langlands.Representation.Archimedean.HilbertIntertwinerEvaluation` makes `J ↦ J x₀` a linear
isometry for the operator norm. `M` is closed (`isClosed_boundedIntertwiners`),
so with this inner product it is a Hilbert space. The map `x ⊗ J ↦ J x` extends to an isometry
`H ⊗ M → E`. Its range is closed and contains every `J x`, so the density hypothesis makes it
unitary. This unitary carries `σ ⊗ I` to `π`.

In this model:

* the relation `X (J x) = J (A x)` says that `X` is `A ⊗ I`. In particular, `A = 0` forces `X`
  to vanish on a spanning set of a dense subspace, so `X = 0`;
* an operator `Y` commuting with `π` is `I ⊗ B`, where `B J = Y ∘ J` (this also follows from
  Theorem 7.11);
* `Q` is `P_v ⊗ I`, where `P_v` is the orthogonal projection onto the line through a unit
  vector `v` of `H`. It commutes with every `I ⊗ B`.

Then `X Y = A ⊗ B` and `Q Y = P_v ⊗ B`. Suppose `A ≠ 0`, and choose unit vectors `u, w` with
`⟪u, A w⟫ ≠ 0`. Compressing `A ⊗ B` between the embeddings `m ↦ w ⊗ m` and `m ↦ u ⊗ m` of `M`
gives `⟪u, A w⟫ B`. Trace-class operators form an ideal, so `B` is trace class whenever `A ⊗ B`
is. Then `P_v ⊗ B` is trace class with trace `tr B`. Computing in a product basis gives
`tr (A ⊗ B) = tr A · tr B`, which is the stated identity.
