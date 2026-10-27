# Algebraic-to-closed irreducibility in an admissible Hilbert realization

Authors: Worker 261.

This module proves the published comparison statement.

The theorem `Langlands.admissibleAlgebraicToClosedIrreducibility` has type
`Langlands.AdmissibleAlgebraicToClosedIrreducibilityStatement.{uG,uV,uH}`.
An admissible, algebraically irreducible representation `ρ` with an
invariant positive form `b` is realized densely in a Hilbert space `H` by a
map `j` that pulls the inner product back to `b`. The theorem shows that the
target action `π` is then topologically irreducible.

## Scope

The theorem adds no hypotheses to the statement. The group, source carrier
and Hilbert carrier keep their independent universes. Compact open subgroups
are cofinal among open subgroups, as the statement requires, and this
hypothesis is passed unchanged to the recovery theorem. The source carrier
has no norm or topology. Neither carrier is assumed finite-dimensional. The
proof uses only continuity of each single operator `π g`. It assumes no
continuity in the group variable, no recovery statement, no injectivity of
`j`, no inner-product preservation by `π` and no irreducibility of the
target. Each of these facts that the proof needs is derived below.

## Implemented proof

**Target action as an algebraic representation.** The proof regards `π` as
a representation `σ : Representation ℂ G H` whose operators are the
underlying linear maps of the `π g`. Equivariance of `j` makes `j` an
intertwiner `J` from `ρ` to `σ`, built with Mathlib's
`LinearMap.intertwiningMap_of_isIntertwiningMap`. Every `σ g` is
continuous. The published theorem `Langlands.admissibleSmoothVectorRecovery`
applies to these data, with the statement's cofinality, admissibility,
density and pullback hypotheses. It states that a target vector has an open
stabilizer exactly when it equals `j v'` for some source vector `v'`.

**Derived facts.** For fixed `g`, the set of pairs `(x, y)` with
`inner ℂ (π g x) (π g y) = inner ℂ x y` is closed in `H × H`. It contains
every pair `(j v, j w)`, by equivariance, the pullback equation and
`b.invariant`. Mathlib's `DenseRange.induction_on₂` extends the identity to
all of `H × H`. The multiplicativity of `π` gives
`π g (π g⁻¹ x) = x`. The map `j` is injective. If `j v = 0`, the
pullback equation gives `b.inner v v = 0`, and positive definiteness
(`b.definite`) gives `v = 0`.

**The target is nonzero.** Algebraic irreducibility is
`IsSimpleOrder (Subrepresentation ρ)`, so the bottom and top
subrepresentations differ. If `V` were a subsingleton, the two would have
the same underlying submodule, so `V` is nontrivial. Choose `v ≠ 0`.
Injectivity gives `j v ≠ 0`, so `H` is nontrivial.

**Closed invariant subspaces.** Let `W` be a closed submodule of `H`
invariant under every `π g`. Since `H` is complete, `W` is complete, and
Mathlib provides its orthogonal projection `P = W.starProjection`, a
continuous linear map `H → H`.

The projection commutes with the action, `P (π g x) = π g (P x)`. The vector
`π g (P x)` lies in `W` by invariance. For `w ∈ W`, write
`w = π g (π g⁻¹ w)`. Inner-product preservation gives
`inner ℂ (π g x - π g (P x)) w = inner ℂ (x - P x) (π g⁻¹ w)`.
This vanishes because `π g⁻¹ w ∈ W`. The uniqueness lemma
`Submodule.eq_starProjection_of_mem_of_inner_eq_zero` then identifies
`π g (P x)` with `P (π g x)`.

The inverse image `W.comap j` is a submodule of `V`. It is
`ρ`-invariant, because `j (ρ g v) = π g (j v)`. So it is an actual
subrepresentation `S` of `ρ`, and irreducibility gives `S = ⊥` or `S = ⊤`.

* If `S = ⊥`, fix `v` and an open subgroup `K` fixing `v`, which exists by
  admissibility. For `k ∈ K`, commutation and equivariance give
  `π k (P (j v)) = P (j (ρ k v)) = P (j v)`. Hence `P (j v)` has an open
  stabilizer. The recovery theorem gives `v'` with `j v' = P (j v)`. This
  vector lies in `W`, so `v' ∈ S = ⊥`. Thus `v' = 0` and `P (j v) = 0`.
  The set where the continuous map `P` vanishes is closed and contains the
  dense image of `j`. By `DenseRange.induction_on`, `P = 0`. For `w ∈ W`,
  `Submodule.starProjection_eq_self_iff` gives `w = P w = 0`, so `W = ⊥`.
* If `S = ⊤`, the range of `j` lies in `W`. Since `W` is closed, it
  contains the closure of that range, which is all of `H` by density. So
  `W = ⊤`.

These two parts are exactly the two components of
`Langlands.Archimedean.IsTopologicallyIrreducible π`.

## Provenance

This is an internal derivation, not a transcription of an external
theorem. It implements the route proposed in the statement's Markdown and in
the task objective, with one difference. The `S = ⊥` case needs no
injectivity: the recovered preimage is itself zero. Injectivity is used only
to show that `H` is nonzero. The proof uses the published recovery theorem
`Langlands.admissibleSmoothVectorRecovery`, the Library definitions it
imports, and Mathlib's orthogonal projection and dense-range lemmas. It
reuses no unreviewed draft. It constructs no Hilbert completion, L2 space,
coefficient embedding, induction model or Mackey decomposition. The opposite
comparison, from closed to algebraic irreducibility, is a separate task.
