# Archimedean control of the middle coordinate of an open cell with a general middle subgroup

The module `Langlands.GroupScheme.Rational.QuadraticLeviCellLocalControl` generalizes
`GaloisCocycle.exists_localCellControl` (module
[`QuadraticTorusCellLocalControl`](QuadraticTorusCellLocalControl.md)) from a torus in the
middle of the cell to an arbitrary affine group `C` over `F`.

## Declaration

`GaloisCocycle.exists_localLeviCellControl` has the hypotheses of
`exists_localCellControl`, with two changes: the middle group `C` is any group over `F` with
affine `C` and `C_Q`, and the torus hypothesis together with the isomorphism `M ≅ ℂ` is
replaced by the hypothesis `hCcb`: there is an open neighbourhood `W` of `1` in `C(M)` such
that every `x ∈ W` with `x · τ(x) = 1` (for the relative Galois action
`GaloisPoint.relativeConjugate F K M C τ`) is of the form `a · τ(a)⁻¹`.

The conclusion is that of `exists_localCellControl` for `C`: for the cocycle `ξ` of `G`,
trivial on the pulled-back cover over `K`, there is a nonempty open set `V` of `M`-points of
`G_Q` such that, for every rational point `f` of `G_Q` in `V`, the twisted value of `ξ` by `f`
at `σ` lies in the cell over `M` at a point `z`, and every cocycle `δ` of `C` on
`Spec Q → Spec F` whose value at `σ` is the middle coordinate `z ≫ p` is trivial on the
pulled-back cover over `K`.

## Proof

The proof is that of `exists_localCellControl`, with the torus neighbourhood replaced by the
supplied `W`. The twisting map `f ↦ f⁻¹ ξ_σ τ(f)` is continuous on `G(M)`; a local cochain
trivializing `ξ` over `K` (`isTrivial_baseChangePullback_iff_quadratic_value`) has twisted
value `1`, which lies in the cell with middle coordinate `1 ∈ W`. The set `V` is the preimage
under the twisting map of the open set of cell points whose middle coordinate is in `W`. For a
cocycle `δ` of `C` with value at `σ` equal to such a middle coordinate `x`, the cocycle equation
gives `x τ(x) = 1`, so `x = a τ(a)⁻¹` and `δ` is trivial over `K`.

## Source

The local step of the proof of Platonov and Rapinchuk, *Algebraic Groups and Number Theory*
(1994), Lemma 6.28 (printed p. 370), for the generalized decomposition of Lemma 6.28'
(printed p. 383); source ID `platonov-rapinchuk-1994-algebraic-groups-number-theory`.
