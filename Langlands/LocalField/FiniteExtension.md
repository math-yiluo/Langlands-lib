# Spectral local-field structures on finite extensions

Let `K : Type u` be a field with a valuative relation, a topology, and
`IsNonarchimedeanLocalField K`. Let `L : Type v` be a field with its
original `K`-algebra structure and `FiniteDimensional K L`. The universes
`u` and `v` are independent. No separability or characteristic hypothesis
is imposed.

All declarations are in `Langlands.LocalField.FiniteExtension`. This
module constructs a norm topology and valuative relation on the original
field `L`; it does not assume a prior topology or valuation on `L`.
The original field operations, algebra map, and scalar action are retained.

## Chosen structures

`normedField K L` is Mathlib's nontrivially normed field structure from the
multiplicative spectral norm of `L/K`. On the base, this uses the published
`LocalGalois.localNormedField K`, whose topology is the given topology of
`K`, together with its proved completeness and ultrametric property.
`normedAlgebra K L` equips the original scalar action with the corresponding
normed algebra structure. These structures are named constructions;
consumers explicitly install them as local instances.

`ultrametric K L` proves that the chosen norm on `L` is nonarchimedean,
using the strong triangle inequality for the spectral norm.

`valuativeRel K L` is the relation obtained from
`LocalGalois.spectralValuation K L` by `ValuativeRel.ofValuation`.
This valuation has values in the nonnegative reals and is defined by the
same spectral norm. Thus `norm_le_iff` identifies norm comparisons on `L`
with comparisons of the values of that valuation by definitional equality.

`algebraMap_vle_iff` proves that the chosen relation restricts to the
original relation on `K` along the original algebra map. Its proof rewrites
the two spectral norm values using `spectralNorm_extends`, compares the
base norm with the original base valuation via
`LocalGalois.localNormedField_le`, and uses compatibility of the base
valuation with the given valuative relation.

## Local-field proof

`isLocalField K L` proves `IsNonarchimedeanLocalField L` after installing
`normedField K L` and `valuativeRel K L`. Its topology is exactly the
topology induced by the chosen spectral norm.

The proof installs the normed algebra and ultrametric structures above.
The spectral valuation is compatible with its constructed relation. The
norm valuation is compatible with the same relation since their
comparisons coincide definitionally. The norm's valued-field structure
and its zero-neighborhood description then give `IsValuativeTopology L`.
Finite-dimensional properness over the locally compact base gives
`ProperSpace L`, hence local compactness. The nontrivial norm valuation
gives a nontrivial valuative relation. These are the required local-field
properties.

## Provenance and use

This is an internal construction from the published local base norm and
spectral valuation in `Langlands.Galois.Local.AbsoluteDefinitions` and
Mathlib's spectral norm, valued topology, and finite-dimensional
properness results. The Lean proof implements the route just described;
no external theorem is supplied as an additional hypothesis.

The construction supplies actual local-field coefficients when applying
local arithmetic to a finite extension, including coefficients of a
restriction of scalars. It proves no classification or Kneser–Tits theorem.
