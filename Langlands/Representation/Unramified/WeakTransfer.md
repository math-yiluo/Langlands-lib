# Arithmetic weak transfer of supplied unramified spectra

This module defines arithmetic comparisons of the published
`Langlands.Unramified.SpectralSystem` over an extension of number fields
`F : Type uF`, `E : Type uE`, with `[Algebra F E]`. The field universes are
independent. Numerical ranks are arbitrary natural numbers, including zero.
The separate actual-class attachment module restricts to positive ranks.

Write `s` for a supplied downstairs system of rank `n` and `t` for an
upstairs system. Each system stores unordered nonzero complex eigenvalues
with multiplicities outside its own finite exceptional set. At a retained
place its Euler denominator is the published `SpectralSystem.eulerPolynomial`,
namely the product of `1 - alpha * X` over those eigenvalues.

`SpectralSystem.IsArithmeticWeakBaseChangeOf t s` compares systems of the
same rank. For cofinitely many actual finite places `v` of `F`, it requires
proofs that `s` is defined at `v` and that `t` is defined at **every**
`w : FinitePlacesAbove E v`. For each such `w`, its actual ramification index
`w.1.asIdeal.ramificationIdx (𝓞 F)` is one, and its spectrum equals
`(s.eigenvalues v hs).power (w.1.asIdeal.inertiaDeg (𝓞 F))`.
The cofinite base-place quantifier precedes the quantifier over all upstairs
places. Thus a single finite base exception set works for every place above
each retained base place.

For ranks `n` downstairs and `m` upstairs,
`SpectralSystem.IsArithmeticWeakInductionOf s t` explicitly requires
`n = m * Module.finrank F E`. At cofinitely many base places it has the
same definedness and ramification-index conditions and requires

```text
s.eulerPolynomial v hs =
  product over w : FinitePlacesAbove E v of
    (t.eulerPolynomial w.1 (ht w)).comp (X ^ f(w/v)).
```

Here `f(w/v)` is exactly `w.1.asIdeal.inertiaDeg (𝓞 F)`.
`inducedEulerPolynomial` names the right-hand polynomial. The product uses
the published finite type of all actual places above `v`; it retains every
place and every eigenvalue multiplicity. Polynomial composition implements
substitution. The definition neither chooses roots nor constructs a
downstairs spectrum or representation. The rank equation is an explicit
condition, rather than a consequence established here by a degree argument.

Both relations use existential proofs of definedness before any comparison.
They assign no values at exceptional places and contain no implication that
could make the comparison vacuous when a required spectrum is absent.

## Original source and normalization

The original source is Arthur and Clozel, *Simple Algebras, Base Change, and
the Advanced Theory of the Trace Formula* (1989), registered as
`arthur-clozel-1989-base-change`, SHA256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The readable file is
`/home/taskhub/central-library/Arthur-Clozel--Simple algebras, base change, and the advanced theory of the trace formula (book)--1989.pdf`.
The relevant passages are Chapter III, printed p.199, Definition 1.1 and
equation (1.1), and printed pp.214–216, Definition 6.1, cases (i)–(iii),
and equations (6.1)–(6.2). These are one-based PDF pages 213 and 228–230;
the formulas on pages 213, 229 and 230 were checked visually.

In III.1.1, the upstairs semisimple Hecke parameter is the residue-degree
power of the downstairs parameter. The unordered multiset equality above
is its supplied-spectrum formulation. The source works with cyclic
extensions; allowing arbitrary extensions in this numerical definition is
a derived extension of the formula, not a claim that Arthur–Clozel proves
an existence or transfer theorem in that scope. We make the common finite
base exception set and definedness conditions explicit.

The induction polynomial is a derived reformulation motivated by III.6.1.
At a split place, every residue degree is one, so the direct sum of the
upstairs parameters gives the product of their Euler denominators, as in
(6.1). At an inert unramified place of degree `l`, (6.2) includes all `l`
roots of each upstairs eigenvalue `alpha`, with all root-of-unity multiples.
Their Euler factors multiply to `1 - alpha * X^l`. This motivates
substitution by `X^f`; multiplying over all actual places also expresses
the intermediate decomposition case mentioned in III.6.1(iii).
This explanation specifies the definition's provenance. The module does
not prove a comparison with local Weil induction or construct the source's
root spectra. The rank multiplication follows the rank in Definition 6.1.
The adjacent Theorem 6.2 existence sentence prints `GL(n, A_F)` although
that definition and the surrounding proof use `GL(n*l, A_F)`; its theorem
is not formalized here.

For genuine automorphic applications the normalization is inherited from
`CuspidalSpectralPresentation` and its
`LocalRealization.HasSphericalHeckeSpectrum` evidence:
`Unramified.standardHeckeScalar` uses the positive square root of the residue
cardinality and the signed Euler coefficients, with integral-subgroup Haar
mass one. The numerical formulas introduce no additional powers of the
residue cardinality. They compare the supplied normalized Satake eigenvalues;
no Hecke-character, Frobenius, or local-correspondence identification is
proved in this module.

## Implemented elementary proofs

`eventually_avoidsAbove` removes the finite image of an upstairs finite set
under the genuine contraction map
`HeightOneSpectrum.under (𝓞 F)`. The published
`finitePlacesAbove_under` identifies that contraction with the tested base
place. This gives one cofinite base set on which **all** places above it
avoid the upstairs set.

The four `isArithmeticWeakBaseChangeOf_restrict_*_iff` and
`isArithmeticWeakInductionOf_restrict_*_iff` theorems show that enlarging
either system's exceptional set leaves each numerical relation equivalent.
From a restricted witness they reuse its values on the original system.
In the other direction they intersect the original cofinite set with the
complement of the enlarged downstairs set, or with `eventually_avoidsAbove`
for the upstairs set. The rank equation is retained in both induction
directions.

`inducedEulerPolynomial_congr_defined` is definitional equality by proof
irrelevance. `inducedEulerPolynomial_restrict` follows from the definition
of restriction. `inducedEulerPolynomial_of_inertiaDeg_eq_one` reduces
composition with `X^1` to the identity.

The three base-change consequences retain one cofinite set uniformly in
the further exponent. `eigenvalues_of_inertiaDeg_eq_one` specializes the
comparison using the existing `Eigenvalues.power_one`; `powers` uses
`Eigenvalues.power_power`; and `powerTraces` uses
`Eigenvalues.powerTrace_power`. None reimplements the power operation or
its algebraic laws. These are elementary consequences of the supplied
comparison, not an arithmetic tower theorem or a self-extension theorem.

## Reused declarations and remaining scope

The implementation imports
`Langlands.Representation.Unramified.SpectralSystem`,
`Langlands.Global.AdelicFunctoriality.Norm`, and
`Langlands.Global.Adelic`. It reuses the published `SpectralSystem.restrict`,
`eigenvalues`, `eulerPolynomial`, `powerTrace`, the `Eigenvalues.power` API,
`FinitePlacesAbove` with its finite-type instance, and
`finitePlacesAbove_under`.

The numerical systems carry no automorphic realization by themselves.
This module proves no existence, cuspidal preservation, uniqueness,
descent, strong local compatibility, tower theorem, or Langlands
correspondence. The existing Hecke-character relation
`SpectralSystem.IsWeakInductionOf` in
`Langlands.Automorphic.Unramified.WeakInduction` is a separate unchanged
interface. Comparing it with the new arbitrary-rank relation requires
genuine Hecke-character spectral realizations and a proved comparison.
