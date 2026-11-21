# Ambient Weil character twists preserve Harris general position

`Langlands.Global.Harris.generalPositionAmbientTwist` proves the published
`Langlands.Global.Harris.GeneralPositionAmbientTwistStatement`. For any
prime `p`, `F : PadicField p`, and finite extension `F'` in the common
algebraic closure, take continuous characters `χ`, `χ'` of the actual
subgroup `W_{F'}` and an ambient continuous character `ψ` of `W_F`. If
`χ'(w) = χ(w) ψ(w)` on `W_{F'}` and `χ` is in general position, the proof
uses the same tower, endpoints, and prime cyclic step witnesses for `χ'`.

For each stage put `H = W_{F'}`, `K = W_{F_i}`, and for each `g ∈ W_F` put
`S = (g H g⁻¹) ∩ K`, viewed as a subgroup of `K`. The private equivalence
first compares the characters on `S`: `conjugateRestriction` evaluates them
at `g⁻¹ s g`, and `ψ(g⁻¹ s g) = ψ(s)` because `ℂˣ` is commutative. Thus
the new inducing line is isomorphic to the old line twisted by `ψ|_S`, by
`twistCharacterLineEquiv`. The proof induces this equivalence and composes
it with `induceTwistEquiv`. The resulting actual representation equivalence
identifies the new Mackey constituent with the old one twisted by `ψ|_K`.
Then `isIrreducible_twist_iff` and
`Weil.IsomorphismInvariance.irreducible_iff` transfer the original
irreducibility for every stage and every ambient group element. No condition
on the stabilizer or order of either character is added.

This is a derived local input for the Proposition 4.8 parity correction, not
an assertion that Harris states a separate twist theorem. The source of the
unchanged tower and constituent conditions is Michael Harris, *The local
Langlands conjecture for GL(n) over a p-adic field, n < p*, Invent. Math.
134 (1998), 177–210, Definition 4.5, p. 201
(registered source [`harris-1998-local-langlands`](https://arxiv.org/abs/math/9611226),
TeX lines 1510–1533).
