# Algebraic boundedness of actual affine rational points

This module defines algebraic boundedness from Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Definition 2.2.1 and Remark 2.2.2, printed
page 70, PDF page 101. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The mandatory corrections, `kaletha-prasad-2024-corrections`, version of
1 November 2024, PDF page 24, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
make the field Henselian throughout Section 2.2. The definition itself does
not require that hypothesis; its later source-level compactness statement
retains it.

The public declarations, in namespace
`Langlands.AlgebraicGeometry.PointTopology`, are:

- `rationalPointAlgebraHom F X p`: the actual algebra map from the global
  coordinate ring of the affine scheme to the field. It composes the
  published identity-test point equivalence with the published affine
  scheme-point equivalence. This adapter is internal derived content,
  introduced only to write the source's evaluation `f(p)` on the existing
  rational-point carrier.
- `IsAlgebraicallyBounded F X B`: for every global regular function `f`,
  there is a nonzero field element `b` such that `f(p) ≤ᵥ b` for all
  `p ∈ B`. Here `≤ᵥ` compares the multiplicative valuation, so the same
  inequality is `ω(b) ≤ ω(f(p))` in the source's additive convention.

The algebra-map adapter assumes no topology. It has a distinct name from
the continuous map `rationalPointEvaluation` in
[RationalPointEvaluation](RationalPointEvaluation.md); that existing map
evaluates the same coordinates after a base-ring topology is supplied.

For a nontrivial real-valued valuation as in the source, the values of
nonzero field elements are cofinal in the multiplicative direction
(equivalently coinitial in the additive direction). Thus choosing a
nonzero field-element bound expresses precisely the source's finite lower
bound. A zero function value satisfies every such multiplicative upper
bound, corresponding to additive value infinity. The definition does
not discard zero values or require the set to be nonempty.

The definition uses every element of the actual global coordinate ring.
It does not select matrix entries, a representation, or a finite set of
coordinates. It is defined for every affine scheme over a valued field;
the source applies it to affine schemes of finite type. Extending the
predicate to other affine schemes adds no compactness claim.

No topology, reductive group, building, parahoric, or compact subgroup is
constructed here. In particular this module does not assert Fact 2.2.3
or prove compactness of any bounded subset. It supplies the regular-function
predicate needed to state that comparison explicitly for the canonical
rational-point topology.
