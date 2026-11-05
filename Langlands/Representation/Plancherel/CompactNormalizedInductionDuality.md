# Haar probability normalization for induced duality

Author: Worker 200.

This module constructs the same-parabolic smooth-dual comparison for actual
normalized induction, with its pairing normalized by Haar probability on a
supplied compact open subgroup. The scalar integration law is proved for that
measure. It is not an analytic hypothesis of the duality constructor.

## Source and provenance

The motivating source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
235–333, DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`:

- I.1, printed p.240 / PDF p.6: the special maximal compact `K`, intrinsic
  subgroup Haar measures normalized by mass one on intersection with `K`,
  and the decomposition `G = P K` for semistandard parabolics.
- I.3, printed p.243 / PDF p.9: positive half-modulus covariance, right
  translation, admissibility of induction, and the bilinear quotient-integral
  identification of induction of the smooth dual with the smooth dual of
  induction.

Both passages were read directly. This module is an internal deduction from
published Library results, in a more general topological subgroup setting.
`RankinSelberg.normalizedCompactOpenHaar` supplies the actual normalized ambient
Haar measure. `ModularCompactAverage.setIntegral_mul_right_eq` proves the scalar
translation identity. `Induction.exists_integralDualEquiv` then constructs the
duality, and `exists_functorEquiv_of_twistEquiv` preserves its integral while
passing to the canonical bundled normalized induction. The argument specializes
these results; it does not assume the source's representation-theoretic
identification or claim a new proof of those imported results.

## Setting and visible hypotheses

For the measure construction, `G` is a locally compact, second countable
topological group with a Borel measurable structure. The supplied
`K : OpenSubgroup G` has compact underlying set, witnessed by `hK`. Neither a
representation nor a parabolic is needed to define the measure.

For `measure_scalar`, `P` is a closed, locally compact subgroup. Assume ambient
unimodularity in the explicit form `hG : ∀ g, modularCharacter g = 1`, and the
actual decomposition

`hPK : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q * k`.

The scalar function `φ : G → ℂ` is locally constant and satisfies
`φ(q*x) = modularCharacter(q) * φ(x)` for every `q : P` and `x : G`.
The modular character here is that of the subgroup `P`, not that of `G`.

For duality, `G` is additionally Hausdorff and nonarchimedean. There are actual
subgroups `P`, `M`, `U` with
`h : IsSemidirectDecomposition P M U`, closedness proofs `hP`, `hU`, and
continuity `hm` of the actual Levi projection `h.projection`. Local compactness
of `P` is an explicit technical typeclass; it is available from closedness in
the locally compact ambient group. The constructor assumes the actual modulus
comparison for all `q : P`:

`modularCharacter q =
  (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0)`.

`A : SmoothRep ℂ M` is admissible. Its carrier universe is independent of the
group universe. The construction uses the canonical smooth algebraic dual,
`smoothDualPairing`, and `normalizedInductionFunctor`; its covariance is the
positive closed half-character and its action is right translation. There is
no irreducibility assumption, including for the induced representation.

## The measure and scalar identity

`CompactInduction.measure K hK` is the comap, along the actual inclusion of `K`,
of `RankinSelberg.normalizedCompactOpenHaar K hK`. The latter is ambient left
Haar with mass one on `K`. The inclusion is an open embedding, so
`measure_isHaar` follows from Haar comap. `measure_isProbability` evaluates the
comap on the whole subgroup and uses the ambient mass-one identity. Thus the
constructed measure is intrinsic Haar probability on exactly this `K`.
It is fixed before any inducing representation, vector, or functional.

`measure_scalar` proves both integrability of `k ↦ φ(k*g)` for every `g` and

`∫ k : K, φ(k*g) dκ(k) = ∫ k : K, φ(k) dκ(k)`.

Integrability follows from continuity and compactness of `K`. The ambient
unimodularity hypothesis, together with
`map_mul_right_eq_modularCharacter_smul`, makes the selected ambient Haar right
invariant. The proof applies the published modular compact averaging theorem
with the same closed `P`, compact open `K`, decomposition and covariance, then
uses `integral_subtype_comap` on each side to obtain integrals on `K`.

## Integral-characterized duality

Write `I(A) = (normalizedInductionFunctor h hU).obj A` and `κ = measure K hK`.
`exists_integralDualEquiv` constructs an actual equivariant linear equivalence

`E : I(A)∨ ≃ I(A∨)`

such that, for every smooth functional `ℓ` and induced vector `f`,

`ℓ(f) = ∫ k : K, (E ℓ)(k)(f(k)) dκ(k)`.

Evaluation is `Induction.eval` on the actual induced function carriers; the
functional application is `smoothDualPairing A.representation`. This is a
complex bilinear identity, without complex conjugation.

The proof obtains compactness of the actual left quotient `P \ G` from the
supplied compact representatives `K`; quotient compactness is not another
hypothesis. It squares the positive closed half-character and uses the modulus
comparison. Closedness of the Levi follows from `hP` and `hm`, giving cofinal
compact open Levi subgroups. The published induction-admissibility theorem
supplies admissibility of `I(A)` from `A.IsAdmissible`. Haar positivity and the
proved `measure_scalar` law now meet every hypothesis of
`Induction.exists_integralDualEquiv`. The final bundled-carrier transport
preserves the same measure and pairing formula.

`integralDualEquiv` chooses this proved equivalence.
`integralDualEquiv_pairing` is its defining integral law, obtained from the
choice specification.

## Scope of this prerequisite

The module applies to general actual subgroup data, without a restriction on
field characteristic, splitness, or quasisplitness. It does not construct the
special compact, reductive decomposition, ambient unimodularity, or modulus
comparison for every reductive rational-point group; those application
obligations remain explicit. The specified `K` need not yet be identified with
Waldspurger's special compact. Product-induction coefficient maps, analytic
estimates, and Plancherel inversion are not established here.

The earlier `normalizedInductionBruhatMeasure` in
`NormalizedInductionDualTensor` has a specification that does not fix its
absolute scale. This module constructs a separate probability-normalized
comparison directly. No equality with that Bruhat measure or equivalence,
independence of compact choice, or replacement of a measure inside an existing
integral witness is asserted.
