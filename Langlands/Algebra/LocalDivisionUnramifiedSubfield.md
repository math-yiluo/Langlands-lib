# An original full-residue subfield of exact residue degree

Let `K` be a nonarchimedean local field with its supplied valuative relation
and compatible topology, and let `D` be a finite-dimensional central division
`K`-algebra. The common universe `u` is arbitrary; there is no characteristic
restriction. Write

```
v = localReducedNormValuation K D,
R = DivisionValuation.Residue v,
k = 𝓀[K],
E(b) = residueGeneratorSubalgebra K D (b : D).
```

The field structure on `R` is `localDivisionResidueField K D`, and its
`k`-algebra structure is exactly `localDivisionResidueAlgebra K D`, induced
by reduction of the original integral scalars. For an original integral
`b : v.integer`, `E(b)` is the actual singleton adjoin inside `D`, equipped
with `residueGeneratorField K D (b : D)`. Its inclusion into `D` is its
original subalgebra inclusion. All declarations are in
`Langlands.CentralDivision`.

## Dimension and generation helpers

The theorem `residueGenerator_adjoin_eq_top` states that the singleton
adjoin of the internal element `⟨a, residueGenerator_mem K D a⟩` in
`residueGeneratorSubalgebra K D a` is the top subalgebra.
The definition `residueGeneratorPowerBasis K D a` constructs its actual
`PowerBasis K (residueGeneratorSubalgebra K D a)`. The theorem
`residueGeneratorPowerBasis_gen` identifies its generator with that
internal element. These three declarations need only that `K` is a field
and `D` is a finite-dimensional division `K`-algebra; they omit the
valuative, topological, local-field and centrality assumptions.

The theorem `residueGeneratorSubalgebra_finrank` says, for every `a : D`,

```
letI := residueGeneratorField K D a
Module.finrank K (residueGeneratorSubalgebra K D a)
  = (minpoly K a).natDegree.
```

This helper needs only that `K` is a field and `D` is a finite-dimensional
division `K`-algebra. It omits the valuative, topological, local-field and
centrality assumptions. Work inside the commutative singleton adjoin:
its internal generator has singleton adjoin equal to the top subalgebra,
by the preimage description of generation. Its power basis computes the
dimension by its internal minimal polynomial. Injectivity of the original
inclusion identifies that polynomial with `minpoly K a`.

The theorem `localDivisionResidue_adjoin_eq_top` takes `z : R` and the
condition that every `y : R` is zero or equals `z ^ n` for some natural `n`.
It proves

```
Algebra.adjoin k {z} = ⊤.
```

The proof uses closure of a subalgebra under zero and powers. The power
condition is an explicit premise of this helper, not an extra premise of
the existence results below.

## Original subfield and polynomial

The theorem `exists_localDivision_fullResidue_polynomial_subfield` produces
`f : Polynomial 𝒪[K]` and an original integral `b : v.integer`. With the
specified field structure on `E(b)`, it proves all six conclusions:

```
f.Monic,
f.map (IsLocalRing.residue 𝒪[K])
  = minpoly k (DivisionValuation.reduction v b),
f.map (algebraMap 𝒪[K] K) = minpoly K (b : D),
IsSeparable K (b : D),
Function.Surjective (localDivisionSubfieldResidueMap K D E(b).val),
Module.finrank K E(b) = Module.finrank k R.
```

Here `localDivisionSubfieldResidueMap` is the map from the actual residue
quotient of the valuation restricted to `E(b)` into the actual residue
quotient of `D`. Thus surjectivity concerns the original subfield and its
original inclusion. There is no supplied subfield, residue generator,
polynomial, separability, or degree hypothesis in this existence theorem.

The corollary `exists_localDivision_fullResidue_degree_subfield` retains
an integral `b`, its separability over `K`, surjectivity of that same residue
map, and the exact displayed equality of dimensions, omitting the polynomial
witness.

## Implemented proof and internal provenance

This pair is internal derived content from the original residue-generator
and exact residue-lift constructions and Mathlib's power-basis and
minimal-polynomial results.

Choose an original integral unit `a` whose residue `z` multiplicatively
generates `R`: every residue is zero or a nonnegative power of `z`.
The residue is nonzero because reduction preserves units. The exact
residue-minimal-polynomial lifting theorem gives `f` and an integral `b`
with reduction `z`, separability over `K`, reduction of `f` equal to
`minpoly k z`, and the image of `f` over `K` equal to `minpoly K (b : D)`.
It also supplies equality of the integral and residue polynomial degrees.

The nonzero reduction of `b` excludes value strictly less than one.
Together with integrality this gives value one, hence an actual unit in
the original integer ring. Its image lies in `E(b)`. The existing
surjectivity theorem for a subfield containing an integral lift of a
multiplicative residue generator therefore applies.

The dimension helper computes `Module.finrank K E(b)` as the degree of
`minpoly K (b : D)`. The monic integral polynomial and its two exact images
identify that degree with the degree of `minpoly k z`. The power condition
on `z` makes its singleton adjoin all of `R`; its residue power basis
identifies this last degree with `Module.finrank k R`. This proves the
claimed exact equality. All choices occur inside the proof.

## Scope

The pair proves existence of an original full-residue subfield whose degree
equals the actual residue extension degree and records the generating monic
integral polynomial. It does not yet prove splitting, normality or cyclicity,
compute ramification, identify this degree with the reduced degree of `D`,
or prove local SK1 or local Kneser–Tits.
