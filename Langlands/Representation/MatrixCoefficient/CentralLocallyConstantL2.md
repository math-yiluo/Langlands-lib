# The locally constant central L² space

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, IV.3.1 Definition, printed p. 99 (PDF p. 105).
II.1.2, printed p. 30 (PDF p. 36), defines `C∞` by local constancy. II.3.5,
printed p. 45 (PDF p. 51), introduces uniform right invariance separately.
The registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`Langlands.Induction.CentralLocallyConstantL2` consists of actual functions
within the published coinduced module for the character of the full center.
The functions are locally constant, with covariance `f(zg) = χ(z) f(g)`.
Centrality gives the source formula `f(gz) = χ(z) f(g)`. Since `χ` has norm one,
`centralCovariantNorm` descends the pointwise norm to the actual center
quotient. Its membership in `MemLp` at exponent two expresses the finite
quotient norm-square integral. The descended norm is locally constant and
hence measurable for the quotient Borel structure.

When the quotient measure is right invariant, the inherited coinduced action
preserves the subspace. It sends `f` to the function `x ↦ f(xg)`. The source
uses a two-sided Haar measure on the quotient, which has this right invariance.

`centralL2ToLocallyConstant` includes the published `CentralL2` by its
underlying functions. Its range consists exactly of the smooth vectors of
the right regular action because a smooth vector has a single open right
stabilizer. The map and its range identify the source's two function
conventions on the same group, character and quotient measure.
