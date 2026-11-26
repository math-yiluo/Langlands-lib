# The degree-zero operator of Waldspurger VIII.2

At the start of VIII.2 (printed p. 321), Waldspurger assumes Theorems VIII.1.1
and VIII.1.2 for every group of strictly smaller semisimple rank. For
\(f\in\mathcal C(G)\) he defines \(\psi\in C^\infty(\Theta)\) by
\(\psi[\mathcal O,P]=0\) if \(P=G\) and \(\psi[\mathcal O,P]=\psi_f[\mathcal O,P]\)
if \(P\ne G\). Finiteness of its support comes from the induction hypothesis and
Remark VIII.1.3 (the printed reference to "Remarque VII.1.3" means VIII.1.3), and
\(\psi\in C^\infty(\Theta)^{\mathrm{inv}}\) comes from Lemma VII.1.4. He then sets
\[{}^\circ f=f-\kappa(\psi),\qquad {}^\circ\mathcal C(G)=\{{}^\circ f;\ f\in\mathcal C(G)\}.\]
This module constructs that operator on the actual rational Schwartz space.
[Waldspurger, *La formule de Plancherel pour les groupes p-adiques* (2003),
p. 321](https://doi.org/10.1017/S1474748003000082)

## Setting

The group is an affine, locally finite type connected reductive group scheme
over a nonarchimedean local field `F` with finite residue field, in any
characteristic and without any split or quasi-split assumption. Rational points
carry the canonical topology. The field universe `u` and the universe `uV` of the
complex representation carriers are independent. The index is the full
semistandard \(\Theta\) of the Library (`RationalSemistandardTheta`), the
truncation is `rationalSemistandardProperFourier` (the actual Fourier family
`rationalSemistandardFourierFamily` composed with
`rationalSemistandardThetaProperPart`), and \(\kappa\) is the actual weighted
synthesis `GlobalSynthesis.invariantSynthesis` on the invariant finite-support
smooth carrier `rationalSemistandardThetaInvariantSections C`.

## Declarations

| Declaration | Content |
| --- | --- |
| `IsWeylInvariant.properPart` | The proper part of a family satisfying `IsWeylInvariant C` satisfies it too. |
| `rationalSemistandardProperFourierInvariant` | The lift \(f\mapsto\psi\), a complex-linear map into `rationalSemistandardThetaInvariantSections C`. |
| `rationalSemistandardProperFourierInvariant_val_val` | Its underlying family is `rationalSemistandardProperFourier f` (by definition). |
| `rationalSemistandardProperFourierInvariant_apply_of_isProper`, `_apply_of_parabolic_eq_top` | The two branches: \(\psi_f[\mathcal O,P]\) for \(P\ne G\), zero for \(P=G\). |
| `rationalSemistandardProperFourierInvariant_support_subset` | The lift is supported in the proper part \(\Theta-\Theta_G\). |
| `rationalSemistandardProperFourierInvariant_eq_of_val` | Any element of the carrier with the same underlying family is the lift. |
| `rationalSemistandardProperFourierInvariant_translate` | The lift intertwines \(\rho(g_1)\lambda(g_2)\) with the carrier's \(G\times G\) action. |
| `rationalSemistandardDegreeZero` | The operator `LinearMap.id - κ ∘ lift`, that is \({}^\circ f=f-\kappa(\psi)\). |
| `rationalSemistandardDegreeZero_apply`, `_apply_apply` | The defining formula, as Schwartz functions and pointwise with `GlobalSynthesis.weightedSynthesis`. |
| `rationalSemistandardDegreeZero_eq_sub` | \({}^\circ f=f-\kappa(v)\) for every carrier element `v` whose underlying family is the truncation of `f`. |
| `rationalSemistandardDegreeZero_eq_self_of_properFourier_eq_zero` | \({}^\circ f=f\) when the truncation of `f` vanishes. |
| `rationalSemistandardDegreeZero_eq_id_of_rank_zero` | In relative semisimple rank zero the operator is the identity. |
| `rationalSemistandardDegreeZero_translate` | \({}^\circ(\rho(g_1)\lambda(g_2)f)=\rho(g_1)\lambda(g_2)\,{}^\circ f\). |
| `rationalSemistandardDegreeZero_translationLaw` | The operator satisfies `RationalDegreeZeroTranslationLaw` of `RationalCuspidalUnit`. |

## The lift and its inputs

`rationalSemistandardProperFourierInvariant` restricts the codomain of the
Library's `rationalSemistandardProperFourierSmooth` to the invariant carrier. Its
inputs are exactly the following.

- *Support.* `hlow : RationalStrictlyLowerRankOrbitFinitenessStatement (relativeRootRank i)`,
  local VIII.1.2 for every actual connected reductive group of relative semisimple
  rank strictly below that of `G`. It reaches the literal proper Levis through
  the proved rank decrease `semistandardProperLeviRank`; no rank function or
  decrease is supplied as data. With geometric finiteness of the index
  `hgeo : Finite (SemistandardSpectralIndex i)` and the proper normal-level
  comparison `hcomp : RationalProperSemistandardNormalLevelFixedComparison K`, this
  is the Library's proper-only VIII.1.3 finite support
  (`rationalProperSemistandardFourierFiniteSupport_of_strictlyLowerRank`). Neither
  same-rank VIII.1.2 nor finite support of the untruncated family is used. This
  input contains no reconstruction assertion.
- *Smoothness.* The full component smoothness target
  `RationalSemistandardFourierFamilySmoothnessStatement` (VII.1.3), with its
  analytic inputs `RationalSemistandardFourierAnalyticInputs` at every component.
- *Invariance.* `hcov : ∀ f, IsWeylInvariant C (rationalSemistandardFourierFamily … f)`.
  This is Lemma VII.1.4 for the actual normalized comparison of `C`, written as the
  pointwise relation that defines the invariant carrier: for every full index
  \((\mathcal O,P)\), Weyl element \(s\), parabolic \(P'\) with Levi \(sM\) and
  point \(\omega\), \(\psi_f[s\mathcal O,P'](s\omega)={}^\circ c_{P'|P}(s,\omega)\,\psi_f[\mathcal O,P](\omega)\).
- *Proper/group split.* `hsplit : SemistandardProperSplitComparisonStatement`, the
  structural statement that rationally conjugate literal Levis are both the whole
  group or both proper (it follows from fixed-torus dynamic coverage by
  `semistandardProperSplitComparison_of_dynamicCoverage`).

`IsWeylInvariant.properPart` is the step from VII.1.4 to the truncated family. The
target index of each comparison arrow of `C` is related to its source index by an
actual Weyl transport (`WeylSectionComparisonData.target_transports`), so by
`Association.Associated.isProper_iff` the two are proper together. On a proper
pair both sides are the untruncated components, and on a group pair both sides
are zero because the comparison is linear.

The remaining parameters are those of the Fourier family (maximal split torus,
generic cocharacter, Iwasawa compact, the matrix representation `rho` used to define
the height, an ambient measure with left and right invariance, its square-integrable
weight, the modular normalizations and the tempered coefficients of the normalized
inductions) and
of the synthesis (cocharacter presentations, finite-index valuation images,
orbit packet data, the common source compact `K0` with the special-compact
properties, geometric fibre finiteness, and the VI.3.1 target
`GlobalSynthesis.SchwartzMembershipStatement`, which places the weighted sum in
the Schwartz space). The operator takes `rho` to be any `MatrixRepresentation`, a
morphism into a general linear group, with no closedness condition. Waldspurger
fixes an algebraic embedding in I.1 (printed p. 242) to define the height; a closed
matrix embedding gives his setting, and the statements that compare
`rationalCuspidalSubmodule` with induced constant terms (for instance the Fourier route of
`RationalSemistandardDegreeZeroConvolution`) request closedness `IsClosedSubgroup rho`
explicitly.

## Independence of the witnesses

The lift has definitionally the underlying family
`rationalSemistandardProperFourier f`, and elements of the invariant carrier are
determined by their underlying family. Hence
`rationalSemistandardProperFourierInvariant_eq_of_val` and
`rationalSemistandardDegreeZero_eq_sub`: for every element `v` of the carrier
whose underlying family is the truncation of `f`, however its finite support,
smoothness and invariance were established, \({}^\circ f=f-\kappa(v)\). The
operator is the actual one; it is not a postulated projection.

## Elementary properties

If the truncation of `f` vanishes, its lift is zero and \({}^\circ f=f\). In
relative semisimple rank zero every semistandard parabolic of the index is `G`
(`rationalSemistandardProperFourier_eq_zero_of_rank_zero` with
`semistandardProperLeviRank`), so the proper part \(\Theta-\Theta_G\) is empty and
the operator is the identity. The truncation is equivariant for the actual
\(G\times G\) actions (`rationalSemistandardProperFourier_translate`), and the
weighted synthesis intertwines that action with \(\rho(g_1)\lambda(g_2)\)
(`GlobalSynthesis.weightedSynthesis_translate`), which gives
`rationalSemistandardDegreeZero_translate` and the translation law used for the
cuspidal unit in the proof of Proposition VIII.4.1.

This module proves no property of the operator that depends on VII.2.5, on
reconstruction, or on analytic comparisons beyond those listed above. The symmetries
of Remark VIII.2.2 for this operator are stated in `RationalSemistandardDegreeZeroSymmetry`
and the convolution identities of Lemma VIII.2.3 in `RationalSemistandardDegreeZeroConvolution`.
This module does not state the comparison of Lemma VIII.2.1. In particular it does not
instantiate `RationalDegreeZeroRangeLaw` of `RationalCuspidalUnit`, which is a predicate on
an arbitrary supplied linear map; only the translation law of that module is proved here
for this operator.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, Journal of the Institute of Mathematics of Jussieu 2 (2003),
235–333, VIII.2, printed p. 321 (PDF p. 87); Lemma VII.1.4, printed p. 317;
Remark VIII.1.3, printed p. 321. Registered source `waldspurger-2003-plancherel`.
[DOI](https://doi.org/10.1017/S1474748003000082)
