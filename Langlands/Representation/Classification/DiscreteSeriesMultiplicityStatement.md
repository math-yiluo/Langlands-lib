# Discrete-series Jacquet multiplicities on the unitary central part

Author: Worker 19.

This document describes proposition definitions, not proved
representation-theoretic results. The actual unitary central part and bundled
Jacquet constructions are imported from the published Library.

`Langlands.GLDiscreteSeriesJacquetMultiplicityStatement` specializes the
discrete-series alternative of Silberger 1979, Theorem 5.4.1.1, to associated
standard Levi subgroups of positive-rank GL_n over finite extensions of Q_p.
The Weyl-count formula applies to the actual unitary central part of each
normalized Jacquet module. The statement also identifies this part by its
tempered irreducible composition factors. It does not assert that the full
Jacquet module has the displayed length.

## Actual hypotheses and objects

The quantifiers range over a prime `p`, a specified `PadicField p` in universe
`uF`, compatible topological data `T`, positive rank `n`, and ordered positive
block shapes `B` and `C` summing to `n`. The actual embedded Levi subgroups must
be conjugate by a permutation matrix: the hypothesis is the published
`CuspidalSupport.LevisAssociated B C`.

For the source and target product Levis, the statement quantifies over Borel
measurable structures on their actual quotients by their full centers and
arbitrary Haar measures `μB` and `μC`. The product topological-group instances
come from `T`. These choices are not empty: the published
`exists_isHaarMeasure_leviCentralQuotient` supplies a Borel Haar measure.
Changing Haar normalization multiplies the relevant integrals by a positive
constant and does not change any integrability condition.

The source action `ρ` is separately required to be irreducible and
`IsSquareIntegrableModCenter ρ μB`. The latter includes smooth admissibility,
a smooth unitary scalar character of the full source center, and square
integrability of every smooth matrix coefficient on the central quotient.
There is no assumption that `ρ` is cuspidal, and no tensor factorization of
the source representation is supplied.

The existing `CuspidalJacquetMultiplicity` wrappers are used solely as bundled
versions of actual constructions; despite their namespace, they accept arbitrary
representations. `I` is normalized upper induction of `ρ`. `Ju` is its normalized
upper `C`-Jacquet module, and `Jo` is its normalized opposite `C`-Jacquet module.
The latter uses the actual lower unipotent radical and inverse full upper
modulus. `Uu` and `Uo` are the restricted actions on `unitaryCentralPart Ju.ρ`
and `unitaryCentralPart Jo.ρ`. The internal `unitaryPart` wrapper is just
`Rep.of` of that subrepresentation, retaining its actual carrier and inherited
linear structure.

The source carrier has universe `uV`, independently of `uF`. Induction, the
Jacquet quotients and their unitary central subspaces have universe
`max uF uV`. A tested constituent has an independent carrier universe `uW`.

## Tempered part without a single central character

An arbitrary sum of tempered irreducible representations can have different
central characters. Consequently the statement does not apply the existing
single-character `IsTemperedModCenter` predicate to that whole sum.

`DiscreteSeriesJacquetMultiplicity.HasTemperedCompositionSeries A μ` means
that there exist a natural number `k` and an actual zero-to-full filtration
`s : ObjectRepFiltration A k` whose graded quotients are irreducible and whose
individual actions satisfy `IsTemperedModCenter ... μ`. This is a property,
not a selected series or an input witness to the main statement. It allows
the zero module, using a length-zero series, and allows nontrivial extensions.
Independence from a chosen series is a Jordan–Hölder theorem obligation; the
definition merely asserts existence.

`UnitaryPartIsMaximalTempered A μ` states, for every actual invariant subspace
`S` of `A`,

```
HasTemperedCompositionSeries (Rep.of S.toRepresentation) μ
  ↔ S ≤ unitaryCentralPart A.ρ.
```

Thus it says both that the concrete part itself has such a composition series
(take `S` to be that part) and that it contains every submodule with tempered
composition factors. The converse also asserts the finite tempered-factor
property for all its submodules. No largest-submodule existence, projection,
decomposition or analytic result is supplied as an object field.

The main proposition asserts this comparison for both `Ju` and `Jo`, under
the discrete-series induction hypotheses. It does not assert it for arbitrary
representations.

## Lengths and constituent multiplicities

Both `Uu` and `Uo` are asserted to be admissible and to have composition length

```
Nat.card (MinimalConjugatingPermutations B C).
```

These are the actual minimal permutations that conjugate the whole embedded
source Levi onto the target Levi; they represent the corresponding right
Weyl cosets once. For each irreducible target-Levi representation `τ` and
each natural number `m`, the proposition asserts, separately for both parts,

```
HasJordanHolderMultiplicity U (Rep.of τ) m
  ↔ m = Nat.card (AssociatingPermutations B C ρ τ).
```

The right-hand set consists of those minimal conjugating permutations whose
actual inverse-conjugation transport of `ρ` is equivariantly linearly
isomorphic to `τ`. Multiple isomorphic transported factors are counted with
their repetitions. The left-hand predicate uses an actual composition
series and counts its isomorphic graded quotients. Setting `m` to the displayed
cardinality asserts existence, and the other implications exclude all other
values. Finite length and the multiplicity formulas are conclusions.

## Original sources and derived correspondence

The main original is A. J. Silberger, *Introduction to harmonic analysis on
reductive p-adic groups* (1979), section 5.4 and Theorem 5.4.1.1, printed
pp.287–288. Literature ID `silberger-1979-harmonic-analysis`; retained PDF
SHA-256 `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
PDF page number is the printed page plus six. Both pages were reread in text
and page images. The bracketed discrete-series case uses the maximal
tempered part and gives length `|W(G/A)|` and the sum of the transported
inducing characters, with the positive Jacquet half-modulus in the source's
unnormalized action.

The following are explicit derived steps, not literal claims about an arbitrary
group in that theorem.

1. The source fixes one Levi and permits different parabolics with that Levi.
   Transport to an associated standard GL Levi identifies its relative Weyl
   indexing set with the actual `MinimalConjugatingPermutations B C`.
   The square-integrable inducing factors stay irreducible, admissible and
   square-integrable under that group isomorphism. The character sum then gives
   the stated multiplicities, by independence of irreducible characters and
   Jordan–Hölder factors. This representation-theoretic argument remains to be
   proved in Lean.
2. The comparison with `unitaryCentralPart` uses Silberger section 4.5,
   printed p.187, especially the weak-exponent definitions and Lemma 4.5.6,
   reread in text and image. In the normalized Jacquet module of an irreducible
   tempered representation, a class exponent is tempered exactly when its
   central exponent is unitary. Discrete series are tempered by Theorem
   4.5.10, pp.188–189; their normalized induction is completely reducible and
   tempered by Lemma 4.5.15, p.191. The comparison extends across this finite
   direct sum and then its Jacquet functor.
3. For a product of GL blocks, the entire algebraic center is the split torus
   of scalar matrices in each block. Thus the source's split-center norm-one
   character condition is the norm-one condition on the full group center
   used by `unitaryCentralPart`. This identification is special to these GL
   Levis; it is not asserted for arbitrary reductive groups.
4. Central generalized-space decomposition for finite-length smooth
   representations identifies the maximal collection of unitary central
   factors with their actual invariant sum. The use of uniform powers follows
   W. Casselman, *Introduction to the theory of admissible representations of
   p-adic reductive groups*, 1 May 1995 draft, section 2.1, p.21, especially
   Proposition 2.1.9. Literature ID `casselman-1995-admissible-representations`;
   retained PDF SHA-256
   `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
   The finite-length representations in this application are center-finite.
   An algebraic character occurring nontrivially in a smooth generalized
   central space has open kernel: on an open central stabilizer of a nonzero
   vector, the uniform-power equation forces the character to be one.
   Consequently the unrestricted algebraic indexing in `unitaryCentralPart`
   does not introduce additional nonsmooth factors here.
5. The use of tempered composition factors is a derived finite-length
   translation of the source's tempered-module terminology, not its literal
   definition. The coefficient definition is on p.184; Lemma 4.5.3,
   pp.185–186, characterizes it by the absolute-value bounds on exponents.
   Those two latter pages were also reread in text and images. Exactness of
   Jacquet functors and generalized-character decomposition make the set
   of exponents of a finite extension the union of those of its factors.
   Nilpotent generalized action may increase polynomial degrees but does
   not change these absolute-value bounds; polynomial growth is allowed by
   the weak inequality in Theorem 4.5.1, pp.183–184. Thus, in the finite-length
   setting, temperedness can be tested on irreducible factors. Central
   decomposition and Lemma 4.5.6 then separate these factors from all
   nonunitary constituents of the Jacquet modules under consideration.
   This yields the stated universal property over invariant subspaces.
   The argument, including the comparison of the irreducible analytic
   `L^(2+ε)` predicate with the source's coefficient criterion, remains to be
   proved in Lean. It does not impose scalar central action on an extension
   or a sum.

Upper induction uses right translation and positive half-modulus covariance.
Upper normalized Jacquet uses the inverse half of the same full modulus.
For the opposite radical, the full modulus is the inverse upper modulus,
so the normalized action uses the positive upper half. The source character
formula is converted to this normalized action before selecting the unitary
part. The maximal-tempered identification in this statement concerns that normalized
action; a raw unnormalized Jacquet action carries the displayed modulus shift
and is not the action to which the norm-one test is applied.

The source uses spectral parameters and analytic continuation to prove the
counting formula. This statement neither replaces that proof by the full cuspidal
geometric-lemma formula nor asserts general irreducibility of reductive tempered
induction. No errata file for these sources was found in the supplied Library.

## Dependencies and remaining obligations

The actual unitary central-part construction, the three efficient Rep
wrappers, analytic predicates, actual induction/Jacquet constructions, Weyl
transport and composition-factor predicates are imported Library constructions.

The full-center/split-center identification, smooth central decomposition,
analytic weak-exponent comparison, finite-length and tempered-induction
inputs, character independence, Weyl-coset parametrization and all stated
representation-theoretic conclusions remain Lean proof obligations. This
statement adds no axiom and assumes no classification or multiplicity
conclusion. Relative regular-parameter comparisons and recovery of inducing
data are separate statement obligations.
