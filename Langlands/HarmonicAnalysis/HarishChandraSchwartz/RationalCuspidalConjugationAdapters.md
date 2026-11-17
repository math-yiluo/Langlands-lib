# Conditional actual-point adapters for Waldspurger VIII.3

This internal construction specializes the published generic reductions in
`CuspidalDecay` and `CuspidalIntegrability` to the actual objects of
`RationalCuspidalConjugationStatement`. Its source motivation is Waldspurger,
*La formule de Plancherel pour les groupes p-adiques* (2003),
Proposition VIII.3.1, printed pp.323–326 (PDF pp.89–92), and Corollary
VIII.3.2, printed pp.326–327 (PDF pp.92–93), registered as
`waldspurger-2003-plancherel`. The adapters do not prove either closed
analytic target.

The field, rational-point topology, actual minimal parabolic, compact open
subgroup, Iwasawa pair and height representation are those of the imported
actual-point modules. All are explicit. No restriction on characteristic,
quasi-splitness or relative rank is added.

`rationalParabolicConjugationChamber` is the preimage of the full
`rationalMinimalChamberInNormKernel` under the minimal parabolic's subtype
map. It is the same actual chamber intersected with actual `G¹`, expressed
on the domain required by `ConjugationIntegralBound`.
`rationalConjugationHalfWeight` restricts the existing `iwasawaWeight` of
the actual `rationalMinimalModulus` to that parabolic.

`rationalConjugationHalfWeight_eq_sqrt` uses the published
`rationalMinimalModulus_eq_one` on `P₀ ∩ K` and `iwasawaWeight_mul` at
`p * 1`. Its squared form follows from `NNReal.sq_sqrt`. This comparison
holds on the whole minimal parabolic and in particular on the chamber;
it identifies the generic squared weight with exactly `δ₀`.

`conjugationIntegralBound_iff_rationalChamberBound` converts between the
generic ENNReal estimate with a nonnegative constant and the real norm
estimate with a strictly positive constant. From the generic bound it
uses `c + 1`, since the modulus and the height power are nonnegative.
Conversely it views a positive real constant as a nonnegative real
constant. The proof transports the inequalities through `ENNReal.ofReal`
and the same ambient representative. Both sides use the totalized
integral; neither asserts convergence.

`rationalCuspidalConjugationBound_iff_generic` applies this equivalence to
the actual intrinsic cuspidal submodule and actual Schwartz functions.
It retains `RationalCuspidalConjugationConverges` on both sides. In
particular a supplied generic bound alone does not prove the complete
local VIII.3.1 conclusion or the closed statement.

## Actual quotient integrability under the supplied analytic hypotheses

`integrable_rationalLeftConjugationPairing_of_conjugationIntegralBound`
specializes the generic countable-cover reduction to the genuine quotient
of the rational points by the actual split centre
`A = (rationalPoints.map s).range`, with `hs : IsSplitComponent s`.
Its complex function is exactly `rationalLeftConjugationPairing`.
It retains all the following inputs:

- Explicit measurable structure on `LeftQuotient A`, the group
  measure `muG` with both left and right invariance, and the quotient
  measure `muQ`. In the source application this is the displayed Borel
  structure of the closed statement.
- Actual Schwartz functions `f₁` and `f₂`, a countable index type, and
  cells `Ω j` covering every point of `LeftQuotient A`.
- Minimal-parabolic points `a j` in the full chamber intersected with
  actual `G¹`, and a representation of every point of `Ω j` by
  `k * a j * y` with `k ∈ K'` and `y ∈ Y`.
- Finiteness of the sets of conjugate functions `f₁^k` and `f₂^(y⁻¹)`,
  and the generic chamber bound for every such pair, using precisely
  `rationalConjugationHalfWeight` and `rationalHeight ρ`.
- The cell-volume inequality
  `muQ (Ω j) ≤ ofReal (C₂ * δ₀(a j)⁻¹)` and summability of
  `(1 + rationalHeight ρ (a j))^(-r)` for a supplied real `r`.
- `AEStronglyMeasurable` of the actual descended complex pairing for
  `muQ`. No measurability of a chosen representative function substitutes
  for this premise.

The representative evaluation law supplies the generic reduction's
function identity on the quotient. Positivity of the Iwasawa weight
and nonnegativity of the actual height supply its sign conditions.
The proved squared-weight identity converts the volume hypothesis.
The existing reduction then gives a finite lower integral of the
pairing's enorm; the displayed a.e. strong measurability premise turns
that result into true Bochner `Integrable`.

This reduction is valid for any `muQ` satisfying its hypotheses. For an
application to the closed VIII.3.2 statement one uses that statement's
explicit central Haar measure `muA` and
`IsCompatible A muG muA muQ`; the cell-volume and measurability hypotheses
must hold for this same compatible `muQ`. Compatibility is not proved or
inferred from a countable cover. The two group-invariance instances are
also explicit inputs to the adapter.

The adapter proves only quotient integrability for its particular pair.
It does not prove convergence of any inner integral. To obtain the
complete local `RationalCuspidalConjugationIntegrability`, one must also
supply `RationalCuspidalConjugationConverges` and establish these quotient
inputs for every intrinsic cuspidal `f₁` and every Schwartz `f₂`.
The imported `rationalCuspidalConjugationIntegrability_iff_right`
then transports the complete local conclusion to the right quotient
under the explicitly transported measure.

The source open-cell and proper constant-term estimates, conjugation
height and tail estimates, I.1 Cartan and volume bounds, compact
conjugation-orbit finiteness, quotient cover and lattice-height
summability remain substantive analytic obligations. Existing tasks
for the intrinsic kernel and its source comparison, constant terms,
Xi estimates, rapid decay and split-centre heights retain their scope.
