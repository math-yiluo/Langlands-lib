# A fixed-group step for Waldspurger VIII.4.2

The step identifies the raw central-integral image of the cuspidal Schwartz
space with the canonical algebraic sum of discrete-series coefficient spaces
for **one** group, Schwartz realization, pair of central and quotient Haar
measures, and continuous unitary character. It uses finite dimensionality of
all central level spans for that realization, central Haar measure and
character. In particular it does not invoke an all-groups VIII.4.1 theorem
from inside a rank induction. It does not prove the local finiteness or the
local radical convergence premise, nor the closed equality target.

## Setting and local convergence

Let `F` be a nonarchimedean local field and `G` a connected reductive group
with maximal split torus `i`, generic cocharacter `ν`, and split component
`s`. The Iwasawa compact open subgroup `K` and closed matrix realization `ρ`
fix the actual `RationalSchwartzSpace hKc hPK ρ`. Write `A_G(F)` for
`(rationalPoints.map s).range`, `muA` for the given Haar measure on `A_G(F)`,
`mu` for the given Haar measure on the quotient `G(F) ⧸ A_G(F)` with its
Borel structure, and `χ` for the continuous unitary character of `A_G(F)`.
There is no normalization premise on either Haar measure.

`RationalSchwartzProperRadicalConvergence hKc hPK ρ` is the local
specialization of `RationalSchwartzConstantTermConvergenceStatement` at the
chosen Schwartz realization, with the quantifiers reordered to match
`DiscreteCoefficientCuspLift.exists_cuspidal_lift`. For every `I` with
`rootSet i ν I ≠ simpleRelativeRoots i ν`, every Haar measure `muU` on
`U_I = standardUnipotentPoints i ν (rootSet i ν I)`, every Schwartz
function `φ`, and all `x, y ∈ G(F)`, it asserts integrability of
`v ↦ φ(x v y)` on `U_I` for `muU`. It does not impose vanishing. The adapter
`RationalSchwartzConstantTermConvergenceStatement.properRadicalConvergence`
specializes the closed proposition if that proposition is given.

## Inclusions and equality

- `rationalCuspidalCentralImage_superset_of_specialCompact` takes a compact
  subgroup `K0` with `SimultaneousStandardBasisAt i ν K0` and
  `FiniteCartanCovering F i ν K0`, and the local proper-radical convergence
  input. It gives the inclusion of
  `discreteSeriesCentralCoefficientSpace.{u, uV}` in the raw
  `rationalCuspidalCentralImage`. Here `uV` is independent of `u`.
  For each class indexed in the coefficient sum, the canonical representative
  is square integrable modulo `A_G(F)` for `mu` and has scalar action `χ`
  on `A_G(F)`. The published `exists_cuspidal_lift` gives, for every element
  of the representative's coefficient space, an actual cuspidal Schwartz
  function with that central projection. The sum of the coefficient spaces
  therefore lies in the span of the raw image by
  `discreteSeriesCentralCoefficientSpace_le_iff`. The span has the same
  carrier as the raw image by `coe_schwartzCentralIntegralSpan_eq_image`,
  using the proved `rationalSchwartzCentralConvergence` on the whole
  Schwartz space and hence on its cuspidal submodule.
- `rationalCuspidalCentralImage_eq_of_specialCompact` also takes openness
  of `K0` and finite dimensionality of
  `rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ J.toSubgroup` for each
  compact open `J`. Its left-hand side is `rationalCuspidalCentralImage`,
  exactly the raw image in `RationalCuspidalDiscreteCoefficientStatement`.
  Its right-hand side is the carrier of
  `discreteSeriesCentralCoefficientSpace.{u, max u uV}` on the same
  quotient and with the same character. The proof uses antisymmetry:
  `rationalCuspidalCentralImage_subset_of_specialCompact` supplies the
  upper inclusion with those local finite-dimensionality hypotheses, and
  the preceding lemma at carrier universe `max u uV` supplies the lower
  inclusion. The upper adapter provides the central weights and `L²`
  weights from the Library's split-centre height results and its proof
  of Lemma II.1.5 from the proved upper bound of Lemma II.1.1. No equality
  of the raw level image with its span needs to be assumed, and no
  reconstruction input occurs in this step.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), DOI `10.1017/S1474748003000082`, VIII.4,
printed pp.327, 330–331 (PDF pp.93, 96–97). The source defines `p_χ` by
integrating `χ(a)⁻¹ f(a g)` over `A_G`, with absolute convergence. Theorem
VIII.4.2 identifies `p_χ(°C(G))` with `A₂(G)_χ`. The proof of its upper
inclusion uses the finite dimension of the individual bi-invariant levels
of Proposition VIII.4.1 for admissibility. The local Lean equality is an
internal version of that step and the lower inclusion; the locality of
its premises is for mutual rank assembly, not an additional claim from
the source. For the weight estimates, see Lemmas II.1.1 and II.1.5,
printed pp.251–252 (PDF pp.17–18).

The lower inclusion does **not** use the wave-packet and Fourier-inversion
argument on printed p.330. It uses the direct lift already constructed in
`RationalDiscreteCoefficientCuspLift`: multiply the coefficient by the
transversal cutoff on `G(F) ⧸ G¹` and divide by the positive `muA`-mass of
`A_G(F) ∩ G¹`. The product step adapts III.7, printed p.273 (PDF p.39),
where the source treats coefficients of admissible square-integrable
representations multiplied by a compactly supported function on `G/G¹`.
The Library lift uses its own coefficient decay and radical-integral
lemmas, with convergence only for the given Schwartz realization.
