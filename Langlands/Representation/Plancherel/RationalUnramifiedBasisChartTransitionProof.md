# Basis independence of the complex chart on unramified characters

`Langlands.Plancherel.rationalUnramifiedBasisChartIndependence_of_basisTransition` proves
`RationalUnramifiedBasisChartIndependenceStatement.{u}`. For a connected reductive
group \(G\) over a nonarchimedean local field, give \(X(G)\) the complex chart
defined by an integer basis \(b\) of the valuation image \(\Lambda(G)\). For any
other integer basis \(b'\), evaluation at \(b'\) is a local biholomorphism
from \(X(G)\) to \(\mathbb C^r\), where \(r\) is the rank of the valuation image.
[Published statement](RationalUnramifiedComplexTorusStatement.md)

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, V.3.20, printed p. 116 (PDF p. 122).
Renard describes \(X(M)\) using the \(\mathbb C^\times\)-valued characters of
the valuation lattice and evaluation on a lattice basis. The theorem covers
the independence of the complex-analytic chart in that description, with the
connected reductive group \(G\) of the published statement in place of \(M\).
The registered source is `renard-2026-representations-groupes-reductifs-padiques`
with SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Proof

Let \(e_b\) and \(e_{b'}\) be the open partial homeomorphisms obtained from the
published open embeddings of the basis coordinates. Each has source all of
\(X(G)\). If \(z\) is in the target of \(e_b\), the character \(e_b^{-1}(z)\)
has \(b\)-coordinates \(z\). In particular, each \(z_j\) is the complex value
of a unit.

The private lemma `contDiffOn_rationalUnramifiedBasisTransition` sends
\(e_b^{-1}(z)\) to the corresponding valuation-image character using
`rationalCanonicalImageUnramifiedContinuousEquiv`. It reconstructs this
character from its unit values on \(b\) via the inverse of
`rationalImageBasisUnitCoordinates`. Applying `rationalImageBasisCharacter_apply`
at \(b'_i\) and coercing the product of units to \(\mathbb C\) gives
\[
  (e_{b'}\circ e_b^{-1})(z)_i
    = \prod_j z_j^{\,b.\mathrm{repr}(b'_i)(j)}.
\]
For a nonnegative integer exponent the factor is a natural power of a
coordinate projection. For a negative exponent it is the reciprocal of a
positive power, which is analytic at \(z\) because \(z_j\ne 0\).
`contDiffAt_prod` and `contDiffAt_pi` give analyticity of the tuple of finite
products. The lemma proves `ContDiffOn ℂ ω` of the transition on the target of
\(e_b\).

The main theorem applies the lemma in both basis orders. Mathlib gives
manifold smoothness of \(e_b\) and its inverse for the singleton charted space.
Composing the forward transition with \(e_b\) proves that evaluation at \(b'\)
is analytic on \(X(G)\). Composing \(e_b^{-1}\) with the reverse transition
proves that the inverse of \(e_{b'}\) is analytic on its target. The inverse
identities of \(e_b\) identify both compositions with the required maps on
their respective domains. The partial equivalence of \(e_{b'}\), its open
source and target, and these two smoothness proofs give a `PartialDiffeomorph`
of order `ω`. Its source contains every point, so the same witness proves
`IsLocalDiffeomorph` at every point of \(X(G)\).
