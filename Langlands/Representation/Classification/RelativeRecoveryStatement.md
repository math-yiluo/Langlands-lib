# Relative recovery of inducing representations

This pair states derived GL_n forms of Silberger 1978, Propositions 5.7 and
5.8. It contains proposition definitions, not proofs. The two assertions
have different support hypotheses, which remain distinct.

## Common fine and middle data

The actual block coordinates and support conventions are those of
`RelativeRegularComparisonStatement`: coarse shape `B`, middle shape
`D = B.flatten Q`, fine shape `C = D.flatten R`, and direct coarse refinement
`S` with the actual shape equality `C = B.flatten S`. That equality transports
the fine representation and parameter; the other transports use the
constructed flattened-Levi equivalence. No arbitrary equivalence is an input.

The fine representation `ω` is irreducible, cuspidal, and unitarizable.
The parameter `v₀` is a strictly positive combination of the adjacent scalar
roots inside each middle block, expressed in determinant coordinates as
`e_j/d_j - e_(j+1)/d_(j+1)`. The middle representation `σ` is irreducible and
square-integrable modulo its full center, and is an actual quotient of
the normalized fine-to-middle induction of `ω |det|^(-v₀)`.
These are the supporting data fixed on Silberger's p.99.

Every coarse real parameter `t` is strictly decreasing. This is the regular
positive chamber for the upper parabolic; individual entries may have
either sign. The fine twist in the ambient group has determinant exponents
`-v₀(k) + t(parent(k))`. The untwisted inner induction uses only `-v₀`.
Upper normalized induction has right translation and positive-half-modulus
covariance, with residue-normalized absolute value `q^(-valuation)`.

`RelativeRecovery.fineAmbientInduced` is actual normalized induction to
`GL_n(F)` from the flattened fine product Levi, with precisely that twist.
It uses the existing determinant character and the existing induction
construction. It is not an assumed induction-in-stages equivalence.

All support and quotient conditions below are actual surjective intertwining
maps. Analytic square-integrability and temperedness quantify over every
Borel Haar measure of the actual product-Levi central quotient; existence
of such measures is already proved. They include admissibility and unitary
central character. No tensor factorization, carrier norm, or canonical
quotient is part of the data.

## Supported recovery: Proposition 5.7

`GLSupportedRelativeRecoveryStatement` takes an irreducible tempered coarse
representation `π`, an actual quotient map from the normalized
middle-to-coarse induction of `σ` to `π`, and an actual quotient map from
the fine-to-coarse induction of `ω |det|^(-v₀)` to `π`.

The competitor `θ` is any irreducible admissible coarse representation that
is also a quotient of that same fine-to-coarse induction. It is **not**
assumed tempered or a quotient of the middle discrete-series induction.
For any strictly decreasing `t`, if the outer inductions of `π |det|^t`
and `θ |det|^t` have a common actual irreducible quotient `J`, the conclusion
is an actual representation equivalence `π ≃ θ`, before twisting.

This is the second assertion of Proposition 5.7. Its first assertion follows
by taking another supported tempered input as `θ`: inequivalent such coarse
inputs cannot have equivalent irreducible outer quotients. Using a common
target `J` is equivalent to using isomorphic quotient targets, since an
isomorphism can be composed with either surjection.

The explicit fine quotient premise on `π` is also present in the preceding
supported all-regular interface; it follows from the two middle support
maps by induction in stages and exactness. It does not assume an outer
quotient or recovery of the inducing representation.

## Arbitrary-tempered quotient reflection: Proposition 5.8

`GLTemperedRelativeQuotientReflectionStatement` allows **any** irreducible
tempered coarse representation `π`. It assumes no quotient map from the
middle induction to `π`, no fine-to-coarse quotient map to `π`, and no
occurrence of `π` as a constituent of either induction.

If an irreducible representation `J` is both an actual quotient of the outer
induction of `π |det|^t` and an actual quotient of
`fineAmbientInduced T B S ω v₀ t`, the conclusion supplies a surjective
intertwiner from the fine-to-coarse induction of `ω |det|^(-v₀)` to `π`.
The middle discrete-series datum constrains the fixed fine support and
parameter, as in the original setup; it places no support premise on `π`.

The source writes `J(π,t)`. The Lean statement quantifies over any irreducible
outer quotient with its actual surjection. The regular-positive
unique-quotient theorem identifies it with the source's `J(π,t)`. This
formulation does not assume head existence or a chosen representative and
does not claim to prove quotient existence as a consequence of these
conditional recovery statements.

`GLRelativeRecoveryStatement` is the conjunction of the two assertions.
The field and the fine, middle, coarse, competing and quotient carriers
have independent universes `uF`, `uV`, `uM`, `uW`, `uX`, and `uZ`.
The reflection assertion has no competing carrier and hence no `uX`.
The actual maps and equivalences allow different carrier universes.

## Original source and the repaired proof boundary

A. J. Silberger, *The Langlands Quotient Theorem for p-adic Groups*,
Mathematische Annalen **236** (1978), 95–104: p.99 support setup;
Lemma 5.6 and Proposition 5.7, p.101 and the first line of p.102;
Proposition 5.8 and its full proof, p.102.
The retained original is
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`,
registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 19 read the entire article, reread pp.99–102, and inspected the
formula images on pp.99, 101 and 102. No retained erratum was located.

For supported recovery, the source uses opposite reciprocity for the two
maps onto `J`, exactness, and the all-regular relative multiplicity equality.
If the two coarse irreducibles differ, their positive inner contributions
give a strict multiplicity inequality, contradicting that equality.
This explains why the competitor need only be an inner quotient, not
tempered. These arguments remain proof obligations.

For arbitrary-tempered reflection, the printed proof first invokes
Corollary 5.4 in the generic case. The unrestricted wording of that corollary
is outside the valid scope identified in the
[published audit](../../../notes/jacquet/silberger-lemma53-scope.md).
The present statement does not claim that the repaired constituent-only
generic comparison immediately applies to the arbitrary `π`.

The retained route is the subsequent continuation and tempered-exponent
contradiction on p.102, applied directly to the relevant fine cuspidal
classes. If the desired inner quotient is absent, opposite reciprocity and
fixed-central-exponent cuspidal extraction force its inner multiplicity
to vanish. The common quotient supplies a positive ambient occurrence.
Continuation and the temperedness of the untwisted outer induction
constrain the Weyl-transformed real exponents. The positive-root support
and regular coarse chamber then force the responsible Weyl element into
the coarse Weyl group, contradicting the zero inner contribution.
Formalizing that implication requires the actual occurrence/continuation
and cone arguments; it cannot be replaced by an invocation of unrestricted
Corollary 5.4 or by assuming that `π` already lies in the fine induction.

Other required inputs include normalized induction in stages, exactness,
finite length, opposite Jacquet transitivity and reciprocity, the
supported all-regular comparison, and regular-positive unique quotients
for the source's use of `J(π,t)`. This pair states the targets only. It
establishes neither those prerequisites nor cosocle multiplicities,
semistandard conjugacy, or final exhaustive classification.
