# Defining sequences

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, (2.4.2)(i)–(vi),
printed pp. 65–66 (PDF pp. 77–78).

`Stratum.IsDefiningSequence S q` is the defining predicate on a finite
family `q : Fin (s+1) → Stratum O K V`, representing the indices
`0 ≤ i ≤ s`. It first requires the original stratum to be pure.
Its clauses implement the six source conditions:

1. Every member has the original chain and level `n`, and is simple.
2. The first member is equivalent to `S`.
3. Its depth is `S.r` and the depths are strictly increasing.
   The inequality `r_s < n` is already a defining condition of
   each `Stratum`.
4. At adjacent indices `i,i+1`, the critical exponent at `γ_i`
   is `−r_{i+1}`, and
   `γ_{i+1}−γ_i ∈ 𝔓^{−r_{i+1}}`. With the common chain and level,
   this membership is exactly equivalence of
   `[𝔄,n,r_{i+1},γ_i]` and `[𝔄,n,r_{i+1},γ_{i+1}]`.
5. The terminal critical exponent is `−n` or `−∞`.
6. For each `1 ≤ i ≤ s`, every tame corestriction relative to
   the actual field `K[γ_i]` gives a derived stratum for
   `γ_{i−1}−γ_i` equivalent to a simple stratum over `K[γ_i]`.

Adjacent pairs are indexed by `Fin s`, using `castSucc` for the
previous index and `succ` for the next. This also covers `s = 0`,
where there are no adjacent or derived conditions.

`Stratum.HasSimpleDerivedStratum` is internal notation for clause
6. It uses `elementAlgebra S.b`, obtains its field structure from
any `IsField` witness, and quantifies all tame corestrictions.
Its conclusion is `DerivedEquivalentToSimple`, which existentially
quantifies both the actual derived stratum and a simple equivalent,
using a chain over `integralClosure O (elementAlgebra S.b)`.
The field witness exists for the simple members of a defining
sequence. No missing centralizer-chain existence is hidden in
an implication.

This predicate defines which families qualify. It does not assume
or prove that any pure stratum has such a family; that existence
is the separate final conclusion of T7. All source conditions
are part of the defining predicate, with no additional structural
or approximation conclusion assumed. The generic `O,K` mechanism
is the same one used for strata over the original field and
over its extension fields.
