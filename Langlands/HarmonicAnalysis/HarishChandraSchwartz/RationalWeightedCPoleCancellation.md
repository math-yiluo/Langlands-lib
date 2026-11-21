# Pole-cancellation reduction for the actual weighted c-family

`Langlands.HarishChandraSchwartz.WeakExpansion.WeightedCExtensionFromPolesStatement`
is a sufficient condition for one `WeightedCExtension` of
`weightedCompactFamily`, for a fixed normalizer lift and its displayed Levi
inclusion. `weightedCExtensionFromPoles` proves that implication. The
representation, source and lower compact pictures, density packages `PG` and
`PM`, and their common compact normalization `hN` are exactly those of
`RationalWeakExpansionTargets`. The field, representation carrier, and
auxiliary normed carrier have independent universes.

## Inputs and conclusion

Write `M₀` for the actual scheme of the inducing standard Levi and `M_I(F)`
for the literal Levi subgroup. Let `Φ : X(M₀) ≃ X(M_I(F))` be unramified
character transport along `leviRationalPointHomeomorph`. Define `D₀` to be the
published `cWeightedDomain`, `Ω = Φ⁻¹(D₀°)`, and `A` on `Ω` by evaluating
`weightedCompactFamily` at the parameter transported by `Φ` with its original
`D₀` membership. Only character parameters are transported; the two compact
carrier spaces are unchanged.

The premises for this fixed family are:

1. `D₀°` is nonempty. A supplied `RationalOperatorContinuationData Ω A` with
   primary denominator `a` and global polynomial numerator `P` has `a ≠ 0`
   at every point of `Ω` and satisfies `P = a • A` there. A presentation on
   only a smaller open set is not enough for this interface.
2. A `RationalOperatorPolePresentation M₀ a P` gives a second regular
   denominator `b` and global polynomial numerator `Q`, with `a • Q = b • P`
   on all of `X(M₀)`. It factors `b` as a list of basis-coordinate root powers
   times a remainder `d` nonvanishing on the entire unitary character group.
   Neither `b` nor `d` is required to be nonzero on `Ω`.
3. For a supplied linear equivalence `e` from the lower compact carrier to
   a complex normed space, `HasClearedUnitaryBound` on the primary presentation
   says that for each source vector `v` there is a real `C ≥ 0` with
   `‖e (P(z) v)‖ ≤ C ‖a(z)‖` at **every** unitary `z`. The estimate concerns
   the numerator, not division at a zero. A bound for the quotient on a dense
   genuine unitary locus would give this estimate by multiplying there and
   applying the Library's `hasClearedUnitaryBound_of_dense` to the polynomial
   numerator postcomposed with `e`.

The conclusion is `Nonempty (WeightedCExtension ... hN)`, with a single
regular denominator nonvanishing at every unitary parameter, and a global
polynomial numerator clearing the original weighted family on **all** of
`D₀°`. It does not assume that the interior contains a unitary point.

## Implemented proof

The private lemma `exists_poleFree_clearing` works on the scheme characters.
The nonempty initial domain gives `a ≠ 0` as a regular function. On the full
nonvanishing locus `D = {z | a(z) ≠ 0}`, continue as `P/a`. The unitary
preimage of `D` is dense by
`ActualCommonLeviV3.dense_rationalUnitaryRegularRestriction_ne_zero`. Dividing
by `‖a(z)‖ > 0` there supplies the per-vector quotient bound required by
`RationalUnitaryPoleFactorization.cancelFromCross`. That published theorem
cancels the supplied factors of `b` and gives a polynomial numerator `N`
clearing `P/a` with denominator `d` on `D ∩ {d ≠ 0}`.

To recover full-domain clearing, note that `d` is nonzero at the trivial
unitary character. Both scalar nonvanishing loci are therefore dense in the
ambient character space by `rationalUnramifiedRegular_dense_nonzero`, and the
second is also open by continuity of regular functions. On their dense
intersection `N = d • (P/a)` and `P = a • (P/a)`. The Library's
`polynomial_operator_cross_eq_of_dense` gives the global identity
`a • N = d • P`. For each original parameter in `Ω`, substitute `P = a • A`
and cancel the **primary** nonzero scalar `a(z)`; thus `N = d • A` even at
zeros of `d` in `Ω`. This does not impose a topology or a continuity assumption
on `A` at those zeros.

Finally the weighted specialization transports `d` and each regular
coefficient in every fixed-vector polynomial for `N` via
`unramifiedRegularFunctionsEquiv`, and precomposes `N` by `Φ⁻¹`. The
transport for unitary characters (`standardLeviUnitaryCharacterHomeomorph`)
commutes with forgetting unitarity. This carries nonvanishing to the literal
Levi unitary subgroup. The proof fills the fields of `WeightedCExtension`
with the transported data and the original `D₀°` nonemptiness proof.

## Source and scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
Lemma V.2.2 and Corollary V.2.3, printed pp.293–294 (PDF pp.59–60), and
IV.1 (12), printed p.283 (PDF p.49). Registered source
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The V.2.3 proof clears local poles by a product of powers of linear forms
indexed by reduced coroots in logarithmic coordinates. It uses V.2.2 on the
regular unitary locus and the product identity for `µ^G/µ^{M′}` to bound the
weighted operator there; minimality and Zariski density in the hyperplanes
then remove the poles. The reduction here is derived: it uses a supplied
**global** Laurent pole presentation and the existing coordinate-root
cancellation theorem instead of the source's local hyperplane argument.
It also preserves the Library extension's clearing identity on the whole
fixed domain interior, rather than just a common nonvanishing locus.

This unit does not construct the primary continuation, prove joint
convergence or nonemptiness of the weighted domain interior, obtain the pole
presentation from the actual intertwiners and density ratio, or prove the
unitary norm estimate. In particular, it does not prove
`WeightedCRegularityStatement` under its original premises. It leaves the
pointwise weak constant-term expansion and packet identity untouched.
