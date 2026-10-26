# Compact last-row cutoff for smooth zero-row Whittaker coefficients

Author: Worker 614.

`Langlands.RankinSelberg.ZeroRowLastRowCutoffStatement.{uF,uV}` is a closed
proposition definition. This module states the compact last-row cutoff
obligation; it supplies no proof.

## Quantifiers and supplied topology

The proposition quantifies over every prime `p`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData`, and every
`n k : ℕ`. It installs precisely the topology, valuative relation, valuative
extension, module-topology certificate, and local-field structure from `T`.
The row space has its finite product topology, and the actual general
linear group has its existing matrix-unit topology for this topology of
`F.Carrier`. The proposition makes no choice of canonical topological data.

For these data it quantifies over:

- every `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`, the
  published continuous nontrivial unit-circle-valued additive character;
- every independent `V : Type uV` with `AddCommGroup V` and `Module ℂ V`;
- every representation `π` of the actual group
  `GeneralLinear (n + (0 + k + 1) + 1) F.Carrier`, under the sole
  representation hypothesis `IsSmooth π`;
- every actual `ℓ : Whittaker.glFunctionals ψ (n + (0 + k + 1)) π`
  and every `f : (Whittaker.coefficientModel π ℓ).toSubmodule`.

The two universes are independent. The published smoothness predicate says
that each vector is fixed by an open subgroup. No topology, norm,
completeness, or finite-dimensionality is imposed on `V`. No irreducibility,
admissibility, square-integrability, nonzero-functional, nonzero-coefficient,
support, or cutoff-existence premise is added. Both `n = 0` and `k = 0`
are included. In particular, the restricted group can have rank one, while
the full group always has at least one additional identity coordinate.
Zero functionals and their zero coefficient models are included.

## Exact conclusion

There exists one actual
`Φ : HarmonicAnalysis.SchwartzBruhat (Fin (n + 1) → F.Carrier)` such that:

- for every row `y`, `Φ y = 0 ∨ Φ y = 1`, as equalities in `ℂ`;
- for every `g : GeneralLinear (n + 1) F.Carrier`,
  `f.val.val (appendIdentity n (0 + k + 1) g) * Φ (lastRow g)
    = f.val.val (appendIdentity n (0 + k + 1) g)`.

Here `SchwartzBruhat` is the existing space of locally constant
complex-valued functions with compact support. `appendIdentity` is the
published monoid homomorphism adjoining the final `0 + k + 1` identity
coordinates, so its value is exactly `diag(g,I_(k+1))`. `lastRow g` is
`j ↦ g (Fin.last n) j`. The nested subtype values `f.val.val` evaluate the
original coefficient-image function. The cutoff depends on that coefficient
and the preceding data, and works simultaneously for every `g`.

Consequently the cutoff is one at every last row where the restricted
coefficient is nonzero. Its value away from those rows is only constrained
to be zero or one. The assertion does not require the restricted coefficient
itself to be compactly supported on the group. It introduces no quotient
norm, quotient measure, Haar measure, second representation, or spectral
parameter, and asserts no integral identity or convergence theorem.

## Source and derived internal scope

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, §8.3, printed pp.450–451, one-based PDF pages 85–86. The retained
original was rendered and read directly, including the displayed matrices:

- registered literature ID: `jpss-1983-rankin-selberg`;
- retained file:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
- SHA256:
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

No source-specific erratum file was found in the supplied project or
published notes. On p.450 the authors show that
`W(diag(g,1)) ≠ 0` forces the last row `η_t g` into a fixed compact
subset of `F^t`, using Iwasawa decomposition and bounds on positive roots.
Page 451 inserts a nonnegative Schwartz function of that row into the
absolute-value integral and applies Cauchy–Schwarz. The source's smaller
rank `t` is `n+1`; its larger rank `r` is
`n + (0 + k + 1) + 1`, so `r-t = k+1`.

The source passage occurs in the square-integrable convergence argument.
The present scope over all smooth coefficient images, together with an
explicit zero-or-one cutoff preserving the original coefficient, is a
derived internal formulation, not a verbatim theorem of JPSS. Compact
last-row support suggests taking a compact open set containing the
relevant rows and its indicator. That would give an actual Schwartz–Bruhat
function with the required values.

A possible direct proof of the smooth scope takes a preimage of `f` in
`V` and uses an open subgroup fixing that vector. Right invariance under
a sufficiently small upper-column subgroup, conjugated by
`diag(g,I_(k+1))`, and Whittaker covariance constrain every nonzero
restricted coefficient's last row to a character annihilator of a fixed
open row lattice. Nontriviality of the additive character is expected to
give a compact bound, followed by a compact open indicator. This is a
prospective proof route only. Neither an annihilator-compactness theorem
nor any cutoff-existence result is assumed by this proposition.

The existing `UnequalRankFourierSmearingStatement` instead averages to a
new coefficient and cuts off the final rectangular matrix row. The current
statement concerns the last row of `g` and the unchanged original
coefficient at zero rectangular rows. It does not use that other
statement as a hypothesis.
