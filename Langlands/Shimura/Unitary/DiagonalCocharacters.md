# Actual diagonal cocharacters and their inner conjugacy classification

This module constructs diagonal scheme cocharacters in the actual complex
Harris group and classifies them under conjugation by actual complex group
points. It identifies the standard diagonal cocharacter with the existing
first-source-factor Kottwitz cocharacter. This is an internal derivation
from `DiagonalPointNaturality`, `DiagonalPointConjugacy`, and the
group-valued Yoneda constructions. The generic helper
`GroupScheme.InnerAutomorphism` constructs the scheme inner automorphisms.
No new source convention or Galois comparison is assumed.

## From natural point homomorphisms to scheme cocharacters

Retain the number fields, compatible algebra towers, central simple unitary
data `D`, and signature charts `C` of `DiagonalPointConjugacy`. Let
`G = D.complexRationalGroupScheme` be the actual iterated complex pullback
of the rational group, and fix predicates
`p : (E →+* ℝ) → Fin n → Prop`.

For each complex test scheme `T`, `diagonalCocharacterPoints C T p`
composes `Gm.pointsEquiv` with `diagonalWeightPointHom`. Thus it is a
homomorphism from the group of actual `Gm` points to `G(T)`. Under the
split point equivalence its value at the unit `u` is

\[
\left((D_{p_\tau}(u))_\tau,u^{-1}\right),
\qquad
D_p(u)=\operatorname{diag}
  (j\mapsto\text{if }p(j)\text{ then }u^{-1}\text{ else }1).
\]

`diagonalCocharacterPoints_naturality` proves naturality under every
test-scheme map by combining the naturality of `Gm.pointsEquiv` with that
of the diagonal point family.

`D.diagonalCocharacter C p` applies `GroupScheme.homOfPoints` to this
proved natural family. Its type is an actual morphism of group schemes

\[
\mu_p:\mathbb G_{m,\mathbb C}\longrightarrow G.
\]

`diagonalCocharacter_points` proves its evaluation formula on all test
schemes using `comp_homOfPoints`. In particular, the multiplication and
naturality laws needed by the construction are proved, rather than supplied
as unverified fields.

## Identification with Kottwitz's cocharacter

Put

\[
r_\tau=
\begin{cases}
n-1&\tau=C.\mathrm{distinguished},\\
n&\text{otherwise},
\end{cases}
\qquad
p_\tau(j)\iff j<r_\tau.
\]

`diagonalCocharacter_kottwitz` proves the equality of scheme morphisms

\[
\mu_p=D.\mathrm{kottwitzCocharacter}(C,\mathrm{true}).
\]

The proof uses `hom_ext_points`, evaluates both maps on every test scheme,
and applies `diagonalWeightPointFamily_kottwitz`. The inverse identity
of `Gm.pointsEquiv` identifies the input point. The Boolean `true` selects
the first source factor and retains the existing
conjugation-before-inversion convention.

## Explicit scheme conjugation

Assume the supports `p,q` have equal cardinalities at every real embedding.
The chosen point conjugator of `DiagonalPointConjugacy`, evaluated on
`Over.mk (𝟙 (Spec ℂ))`, is an actual complex group point `g`.
The theorem `diagonalWeightPointConjugator_constant` proves that its
pullback to any `T` is the previously constructed conjugator on `T`.
This follows directly from the conjugator's pullback naturality.

`diagonalCocharacter_conjugate_of_card_eq` proves

\[
\mu_p\mathbin{\gg}\operatorname{Int}(g)=\mu_q
\]

as an equality of group-scheme homomorphisms.
Here `Int(g)` is `GroupScheme.innerIso`, whose action is
`x ↦ g_T x g_T⁻¹`. The proof tests the morphisms on all points, uses the
evaluation formulas for the cocharacters and inner automorphism, replaces
the constant point by the chosen point conjugator, and applies
`diagonalWeightPointConjugator_spec`.

## Exact classification and the signature criterion

`DiagonalCocharacterConjugate C p q` is the proposition asserting the
existence of an actual complex point `g` with the preceding equality.
It allows arbitrary complex group points as conjugators.
`diagonalCocharacterConjugate_iff_card_eq` proves

\[
\mu_p\text{ is inner-conjugate to }\mu_q
\quad\Longleftrightarrow\quad
\#\{j:p_\tau(j)\}=\#\{j:q_\tau(j)\}\quad\text{for every }\tau.
\]

Sufficiency uses the explicit point and scheme equality just constructed.
For necessity the proof evaluates the assumed scheme equality on the
base test scheme `Spec ℂ`, at every `Gm` point. Nontriviality of its
global section ring follows from the actual `Scheme.ΓSpecIso` with `ℂ`.
The resulting simultaneous point-family conjugacy gives the cardinality
equalities through `diagonalWeightPointConjugate_iff_card_eq`.
Consequently the scheme theorem needs no additional global-section
nontriviality hypothesis.

`diagonalCocharacterConjugate_kottwitz_iff` specializes this classification:
an actual complex point conjugates the first-factor Kottwitz scheme
cocharacter to `μ_q` exactly when

\[
\#\{j:q_\tau(j)\}=r_\tau\quad\text{for every }\tau.
\]

Its proof substitutes the scheme Kottwitz identification, applies the
classification, and computes initial-segment support sizes using
`Fin.card_filter_val_lt` and `rτ ≤ n`.

These are actual scheme cocharacters and scheme conjugacies in fixed Harris
charts. The classification covers the specified inverse/trivial diagonal
families. Chart independence, the Galois action, and comparison with the
reflex stabilizer remain further obligations.
