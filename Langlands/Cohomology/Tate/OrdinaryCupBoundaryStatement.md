# Ordinary tensor cup and connecting maps

Author: Worker 45.

`Langlands.Tate.OrdinaryCupBoundaryLaws` states the two connecting-map laws
for the independently constructed `ordinaryCup`, specialized to the actual
equivariant tensor pairing. It quantifies over a commutative ring `R`, an
arbitrary group `G`, representations in a common arbitrary universe `u`, and
all natural degrees `p,q`, including zero.

For a short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0`, the first clause
assumes that its tensor product on the right by `B` is also short exact.
For `a ∈ H^p(G,X₃)` and `b ∈ H^q(G,B)`, it states

```text
(δ a) cup b = δ(a cup b).
```

The left side uses `ordinaryCup (tensorPairing X₁ B) (p+1) q`. The right
side uses the actual ordinary connecting map of `S` tensored by `B`.
The explicit `eqToIso` transports its degree `(p+q)+1` to `(p+1)+q` in
actual `groupCohomology (X₁ ⊗ B)`.

The second clause assumes that tensoring `S` on the left by `A` is short
exact. For `a ∈ H^p(G,A)` and `b ∈ H^q(G,X₃)`, it states

```text
a cup (δ b) = (-1 : R)^p • δ(a cup b).
```

The left side uses `ordinaryCup (tensorPairing A X₁) p (q+1)`. The right
side uses the actual ordinary connecting map of `A` tensored with `S`.
Again the degree transport is explicit, from `(p+q)+1` to `p+(q+1)`.
The sign is determined by the degree of the first input. Both connecting
maps in each clause are Mathlib's `groupCohomology.δ`; each is supplied
with the corresponding short exactness proof.

Only the two indicated short exactness hypotheses are imposed in either
clause. There is no universal flatness, scalar splitting, or finiteness
assumption. In particular this target does not impose flatness on either
input of the scalar pairing used in the parent Tate application. Scalar
split coefficient shifts can later establish the required tensor exactness.

The signs and tensor-exactness conventions are those of Serre, *Local Fields*
(1979), VIII §3, Proposition 5(iii)–(iv), printed p.131 (PDF p.137).
Serre's proposition concerns integral finite-group Tate cohomology. This
statement is an internal ordinary-cohomology compatibility target for the
published explicit cochain cup and its signed Leibniz identity, extended
to the commutative-ring and arbitrary-group setting of that construction.
It does not assert that Serre states this broader formulation. The
normalization and coefficient-naturality target is `OrdinaryCupLaws` in
`OrdinaryCupStatement`. The present file states the boundary laws; it
contains no proof and makes no ordinary-to-Tate comparison claim.
