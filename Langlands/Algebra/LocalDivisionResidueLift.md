# Integral residue lifts with the exact minimal-polynomial degree

Let `K` be a nonarchimedean local field with its supplied valuative relation
and compatible topology, and let `D` be a finite-dimensional central division
`K`-algebra. Their common universe `u` is arbitrary and the characteristic
is unrestricted. Write

```
v = localReducedNormValuation K D,
R = DivisionValuation.Residue v,
k = 𝓀[K].
```

Here `R` is the actual quotient of the original integer subring by its
strict-value ideal, with field structure `localDivisionResidueField K D`.
Its `k`-algebra structure throughout this pair is exactly
`localDivisionResidueAlgebra K D`, induced by the original scalar inclusion
and reduction. Thus `minpoly k z` below uses this specified residue action.
All declarations belong to `Langlands.CentralDivision`.

## Original integral scalars in an embedded field

An auxiliary field `L : Type uL`, with independent universe `uL`, has its
original `K`-algebra structure and an actual embedding `ι : L →ₐ[K] D`.
Write `vL = localDivisionSubfieldValuation K D ι` for the restriction of `v`.

The definition `localDivisionSubfieldBaseIntegerMap K D ι` is the ring map

```
𝒪[K] →+* vL.integer
```

whose underlying function is `a ↦ algebraMap K L (a : K)`. The theorem
`localDivisionSubfieldBaseIntegerMap_reduction` states, for every `a : 𝒪[K]`,

```
localDivisionSubfieldResidueMap K D ι
  (DivisionValuation.reduction vL
    (localDivisionSubfieldBaseIntegerMap K D ι a))
  = localDivisionBaseReduction K D a.
```

Neither construction requires finite dimensionality of `L` or surjectivity
of its residue map.

With `[FiniteDimensional K L]`, the theorem
`localDivisionSubfield_lift_base_polynomial` takes the following inputs:

- Surjectivity of `localDivisionSubfieldResidueMap K D ι`.
- A monic polynomial `f : Polynomial 𝒪[K]`.
- An actual residue element `z : R` with
  `f.eval₂ (localDivisionBaseReduction K D) z = 0` and
  `f.derivative.eval₂ (localDivisionBaseReduction K D) z ≠ 0`.

It produces `b : vL.integer` such that

```
f.eval₂ (localDivisionSubfieldBaseIntegerMap K D ι) b = 0,
localDivisionSubfieldResidueMap K D ι
  (DivisionValuation.reduction vL b) = z.
```

The root is in the original embedded field with its original operations.

## Minimal polynomials and integral lifts

For every `z : R`, the theorem
`exists_localDivision_residue_minpoly_polynomial` produces a polynomial
`f : Polynomial 𝒪[K]` satisfying all four assertions:

```
f.Monic,
f.map (IsLocalRing.residue 𝒪[K]) = minpoly k z,
f.natDegree = (minpoly k z).natDegree,
Irreducible (f.map (algebraMap 𝒪[K] K)).
```

The theorem `exists_localDivision_residue_minpoly_lift` additionally produces
an original integral `b : v.integer`. Its precise joint conclusion is

```
f.Monic,
f.map (IsLocalRing.residue 𝒪[K]) = minpoly k z,
f.natDegree = (minpoly k z).natDegree,
f.map (algebraMap 𝒪[K] K) = minpoly K (b : D),
DivisionValuation.reduction v b = z,
IsSeparable K (b : D).
```

There is no additional premise choosing a subfield, generator or root.
In particular the corollary `exists_localDivision_residue_degree_lift`
states that every `z : R` has an original integral lift `b` with

```
DivisionValuation.reduction v b = z,
IsSeparable K (b : D),
(minpoly K (b : D)).natDegree = (minpoly k z).natDegree.
```

This includes `z = 0` and imposes no perfectness assumption on `K`.

## Implemented proofs and internal provenance

This is internal derived content from the actual norm valuation, residue
scalar embedding, full-residue commutative subfield and Hensel constructions,
and Mathlib's polynomial lifting, finite-field separability, Gauss's lemma
and minimal-polynomial results.

For the integral scalar map, the restricted value of a scalar is its original
base value raised to the positive reduced degree. An integral scalar remains
integral. The embedding's scalar compatibility then proves the displayed
reduction equation. In the polynomial lifting theorem, choose a preimage of
`z` in the subfield residue. Apply the injective residue inclusion to the
polynomial evaluation to obtain the root equation there. Its derivative
cannot vanish, because its image is the assumed nonzero derivative at `z`.
The actual Hensel theorem in `vL.integer` lifts this simple root.

The residue carrier is finite. Hence `R` is integral over its specified
base residue field, and that finite base field is perfect. The minimal
polynomial of `z` is therefore monic, irreducible and separable. Surjectivity
of original scalar reduction and
`Polynomial.lifts_and_natDegree_eq_and_monic` give a monic polynomial with
exactly this reduction and degree. A monic polynomial with irreducible
reduction is irreducible over the base integer domain. That domain is
integrally closed and has fraction field the original `K`, so the monic
Gauss lemma proves irreducibility over `K`.

Choose an actual full-residue commutative subfield using
`exists_residueGeneratorSubfield K D`. The residue minimal polynomial has
`z` as a root, and separability makes its derivative nonzero there. Reduction
commutes with scalar evaluation and differentiation, so the preceding Hensel
lifting theorem applies to the monic integral polynomial in that subfield.
Map its lifted integral root into the original integer subring of `D`.
The scalar evaluation equation is preserved under this inclusion.
Irreducibility and monicity over `K` identify the mapped polynomial with the
actual `minpoly K (b : D)`.

Finally, its derivative is nonzero over `K`: otherwise injectivity of the
integer inclusion would make the integral derivative zero, contradicting its
nonzero residue evaluation. For an irreducible polynomial over a field,
this proves separability. Monicity also preserves degree under the integer
inclusion, giving the corollary's exact equality.

## Scope

The pair constructs original integral separable lifts with the displayed
minimal-polynomial and degree identities. It does not yet identify the
degree of a full-residue subfield with a residue extension degree, compute
ramification, prove cyclicity or reduced-degree maximality, or establish
local SK1 or the local Kneser–Tits theorem.
