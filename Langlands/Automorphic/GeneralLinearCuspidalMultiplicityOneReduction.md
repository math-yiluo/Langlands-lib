# Multiplicity one for the cuspidal spectrum of `GL_n`, reduced to three named premises

Module `Langlands.Automorphic.GeneralLinearCuspidalMultiplicityOneReduction`,
namespace `Langlands.Automorphic.GroupSchemeFunctions`. This is a conditional reduction of
multiplicity one for the cuspidal spectrum of `GL_n`. It does not prove `GeneralLinearCuspidalMultiplicityOneStatement` outright: the
main theorem takes three propositions as hypotheses.

## Main theorem

```
theorem generalLinearCuspidalMultiplicityOne_of_summandEquivalence
    (hOne : Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement.{u})
    (hReal : GeneralLinearCuspidalSummandRealizationStatement.{u})
    (hEquiv : GeneralLinearCuspidalSummandEquivalenceStatement.{u}) :
    GeneralLinearCuspidalMultiplicityOneStatement.{u}
```

The three premises are:

1. `Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement` (published, module
   `Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement`): over a number field whose
   adele quotient is compact, two cuspidal operator realizations of the same rank that are
   equivalent (`Nonempty (T.Equivalence T')`) have the same realization, that is, the same
   space of forms.
2. `GeneralLinearCuspidalSummandRealizationStatement` (published, module
   `Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationStatement`): every nonzero,
   closed, invariant and minimal submodule `P` of the full almost-everywhere cuspidal subspace
   `S` of `L²` of the positive-central rational quotient of `GL_{r+1}` is the closure of the
   image of a linear map `Φ : R.Space → S` for some cuspidal operator realization `R`, where
   `Φ` sends every form to the `L²` class of the function it induces on the quotient
   (`IsGeneralLinearFormClass`).
3. `GeneralLinearCuspidalSummandEquivalenceStatement` (module
   `Langlands.Automorphic.GeneralLinearCuspidalSummandEquivalenceStatement`, ported together
   with this module): if `P` and `Q` are two such minimal submodules with an isometric equivalence
   `U : P ≃ Q` intertwining the right regular action, and `R, Φ` and `R', Φ'` realize `P` and
   `Q` as in premise 2, then `R` and `R'` are equivalent. Its Markdown states it in full and
   explains its provenance.

None of the three premises is proved here. Premise 1 is proved in the Library as
`cuspidalOperatorMultiplicityOne` (module `Langlands.Automorphic.CuspidalOperatorMultiplicityOneProof`).
Premises 2 and 3 are not proved in the Library; premise 2 follows from the density statement
`GeneralLinearSummandFormsDenseStatement` by `generalLinearCuspidalSummandRealizationFromDensity`.

## Local instances

`multiplicityOneReductionGeneralLinearIsAffine` and `multiplicityOneReductionGeneralLinearSmooth`
supply `IsAffine` and `Smooth` for `GroupScheme.GeneralLinear.groupScheme (Fin n)
(CommRingCat.of F)` from the published `isAffine_groupScheme` and `smoothStatement`, as in the
imported statement modules. They have new names so that the module can import those modules.

## Helper lemmas (namespace `GeneralLinearCuspidalMultiplicityOne`)

* `lp_eq_smul_of_subsingleton`: on a measurable space `α` with at most one point, for every
  measure `ν` and `f, g ∈ L²(ν)` with `f ≠ 0`, there is `c : ℂ` with `g = c • f`. If `α` is
  empty, every class is `0`, contradicting `f ≠ 0`. Otherwise let `x₀` be the point. The
  representative of `f` is nonzero at `x₀` (else `f` would be `0`), and
  `c = g(x₀) / f(x₀)` works, checked almost everywhere with `Lp.coeFn_smul`.
* `submodule_le_of_subsingleton` and `submodule_eq_of_subsingleton`: for such `α` and a
  submodule `S` of `L²(ν)`, a nonzero submodule `Q` of `S` contains every submodule `P` of `S`
  (each element of `P` is a multiple of a nonzero element of `Q`), so two nonzero submodules
  of `S` are equal.
* `subsingleton_adelicGroupPoints_zero`: the adelic points of `GL_0` form a one-point group,
  through the published homeomorphism `GeneralLinearGroupPoints.adelicHomeomorph F 0` with
  the units of the `0 × 0` matrices.
* `subsingleton_positiveRationalQuotient_zero`: hence the positive-central rational quotient of
  `GL_0` has at most one point (`LeftCosetSpace.mk_surjective`).
* `isGeneralLinearFormClass_unique`: if `IsGeneralLinearFormClass F r T i φ f` and
  `IsGeneralLinearFormClass F r T i ψ f`, then `φ = ψ`. The two continuous functions `h, h'`
  on the quotient have the same pullback `f` under the injective maps
  `continuousGeneralLinearEquiv` and `positiveQuotientContinuousPullback`
  (`positiveQuotientContinuousPullback_injective`), so `h = h'`, and `φ` and `ψ` both agree
  with `h` almost everywhere.
* `range_eq_of_realization_eq`: if two cuspidal operator realizations `R, R'` have equal
  `realization` fields and `Φ : R.Space → S`, `Φ' : R'.Space → S` both send forms to their
  `L²` classes, then `range Φ = range Φ'`. After substituting `R'.realization = R.realization`
  (the remaining fields of `CuspidalOperatorRealization` are proofs), `Φ f = Φ' f` for every
  `f` by `isGeneralLinearFormClass_unique`.

## Proof of the main theorem

Fix a number field `F` and `n`.

* `n = 0`. All hypotheses of the target are introduced. By
  `subsingleton_positiveRationalQuotient_zero`, the quotient carrying `L²` has at most one
  point, and `P, Q` are nonzero submodules of `S`; `submodule_eq_of_subsingleton` gives
  `P = Q`. No premise is used. (The minimality, closedness, invariance and `U` are not
  needed.)
* `n = r + 1`. The instance `CompactSpace (AdeleQuotient F)` is supplied by the published
  `compactSpace_adeleQuotient`. Premise 2 applied to `P` and to `Q` gives `R, Φ` with
  `closure (range Φ) = P` and `R', Φ'` with `closure (range Φ') = Q`. Premise 3, applied to
  `P, Q, U` and these realizations, gives `Nonempty (R.Equivalence R')`, and premise 1 gives
  `R.realization = R'.realization`. By `range_eq_of_realization_eq`, `range Φ = range Φ'`, so
  `P = closure (range Φ) = closure (range Φ') = Q`.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## What is not proved or used

The three premises are hypotheses and are not proved here. The prerequisites of
Getz–Hahn's route are density and realization of smooth vectors (with the
Whittaker expansion), nonvanishing of the Whittaker functional, local uniqueness of Whittaker
functionals and the factorization of global Whittaker functionals. This module neither proves
nor uses any of them directly. Where they are needed, they enter through the premises: the
Whittaker part through premise 1 (whose Library reduction uses
`CuspidalWhittakerModelComparisonStatement`), and the passage from `L²` to forms through
premises 2 and 3.

## Provenance

The reduction is internal. Its main idea is the one of the sources: multiplicity one in
`L²_cusp` reduces to multiplicity one for the cuspidal automorphic representations formed by
cusp forms, after identifying each irreducible summand with the closure of its `K`-finite
vectors. The proof in Getz–Hahn compares Whittaker functionals on the two realizations; here
that comparison is packaged in premise 1, and the passage between the `L²` and form models
in premises 2 and 3. The case `n = 0` is a direct computation that the sources do not treat.

## Sources

* J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, Graduate Texts in
  Mathematics 300, Springer, 2024 (registered source
  `getz-hahn-2024-automorphic-representations`), Theorem 11.4.3 and its proof, p. 303 (PDF
  p. 314): an irreducible admissible representation of `GL_n(𝔸_F)` occurs with multiplicity at
  most one in `L²_cusp([GL_n])`; the proof compares two realizations of a cuspidal automorphic
  representation and concludes `V_1 ∩ V_2 ≠ 0`, hence `V_1 = V_2`.
* J. R. Getz and H. Hahn, *Errata for An Introduction to Automorphic Representations*, October
  2026 (registered source `getz-hahn-2024-errata-2026-10`): its only Chapter 11 entry (p. 3)
  concerns §11.5, so no correction affects Theorem 11.4.3.
* J. A. Shalika, *The multiplicity one theorem for GL_n*, Ann. of Math. 100 (1974), 171–193
  (registered source `shalika-1974-multiplicity-one`), §5, Theorem 5.5, p. 187 (PDF p. 18):
  each irreducible unitary representation of `G_A` occurs with multiplicity at most one in the
  space of cusp forms `𝒞_ρ`.
