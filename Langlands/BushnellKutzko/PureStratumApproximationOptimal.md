# An optimal candidate approximation

Source context: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, proof of (2.4.1)(i), printed p. 67 (PDF p. 79), just before (2.4.5). The source chooses a simple stratum satisfying (2.4.3) whose generated field has maximal degree, and then takes the depth minimal. It later relies on compactness to stop the resulting iteration (printed pp. 69–70). `OptimalCandidateStatement` makes the same choice in the Library's chain model, with the depth normalized by the period, so that a minimum exists without compactness. This is a derived statement.

## Statement

`OptimalCandidateStatement` is a closed proposition over every nonarchimedean local field `F` and finite-dimensional `F`-space `V`. Fix a pure stratum `S` with element `β`. Call a stratum `T` a candidate if it is simple, `β ∈ T.coset`, and `[F[T.b]:F] < [F[β]:F]`. If some candidate exists, there is a candidate `T₀` with these properties:

- every candidate `T` has `[F[T.b]:F] ≤ [F[T₀.b]:F]`;
- every candidate `T` with `[F[T.b]:F] = [F[T₀.b]:F]` has `T₀.r · e(T) ≤ T.r · e(T₀)`, that is, `T₀.r / e(T₀) ≤ T.r / e(T)`.

Here `e(T)` is the period of `T.chain`.

## Implemented proof

Candidate degrees are natural numbers below `[F[β]:F]`, so `Nat.findGreatest` gives the maximal achieved degree `d`. Every period divides `K = (dim_F V)!`, by `period_le_finrank`. So each normalized depth `T.r / e(T)` is the integer `T.r · (K / e(T))` divided by `K`. `candidateDepthBound_aux` gives `m` with `m · e(T) ≤ T.r` for every candidate, since a simple stratum is pure. Hence these integers are at least `m · K` for all candidates of degree `d`. `Int.exists_least_of_bdd` gives a candidate of degree `d` attaining the least such integer. Clearing the positive factors `e(T₀) · e(T)` and `K` turns that minimality into the stated cross-multiplied inequality.
