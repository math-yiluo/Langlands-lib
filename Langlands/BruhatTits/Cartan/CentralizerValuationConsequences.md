# Intrinsic image and kernel comparisons for the normalized valuation

This definition unit supplies the algebraic adapters for the actual centralizer
valuation image. It retains the explicit bijectivity argument `h` for the
actual restriction-evaluation map. No building or Cartan conclusion occurs in
that argument. The surrounding Cartan statements impose the actual maximal
split torus and represented-centralizer conditions.

`centralizerValuation_ker` identifies the transported valuation kernel with
`rationalCommonNormKernel Z`. The proof observes that composition with an
injective inverse linear equivalence preserves a kernel, then uses the
published kernel law for `rationalNormLogarithm`. For the actual centralizer
this is the character-valuation kernel `Z(F)^1`. It is not an identification
with the generally smaller `Z(F)^0` in KP's parahoric Cartan bijection.

`centralizerValuationQuotientEquiv` uses that kernel equality and the first
isomorphism theorem to identify `Z(F)` modulo the actual common norm kernel
with the actual subgroup `centralizerValuationImage s h` in `V(S)`.
`centralizerValuationImageEquiv` composes its inverse with the existing
`rationalNormKernelQuotientEquiv Z`. It is consequently an equivalence to the
actual `rationalCharacterValuationImage Z` in the integer dual of rational
characters. The two pointwise laws specify both equivalences on every actual
rational point. These are algebraic equivalences; no topology, discreteness,
finite rank, finite index or full integral cocharacter lattice is asserted.
They do not assert that maximal-compact double cosets equal either quotient.

`centralizerValuation_id_eq_split` compares the normalized valuation with the
published `SplitTorusValuation.realValuation` on the coordinate split torus.
It applies uniqueness of the character normalization and the published split
valuation's character-evaluation identity. It retains the displayed comparison
argument for the identity embedding; the general comparison is a separate
statement target. In particular the equality fixes the positive sign.

The provenance is internal algebraic transport from
`CentralizerValuation`, the Library's positive rational-character valuation
and its quotient-to-image equivalence, and the published split-torus
normalization. The source conventions are Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), §2.6(d), printed pp.102–103/PDF133–134, especially
(2.6.3)–(2.6.4), and §5.2, printed p.187/PDF218, with *Corrections and
additions*, 1 November 2024, PDF24–25 and 30. Character order is positive and
the dominant inequalities are nonnegative. The actual geometric translation
comparison, where applicable, uses the negative of the projected positive
valuation; this module constructs no root-valuation translation.
