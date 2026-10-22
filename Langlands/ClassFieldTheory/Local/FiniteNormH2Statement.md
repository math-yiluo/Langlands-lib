# Relative H2 vanishing from all intermediate-field norms

`Langlands.ClassFieldTheory.Local.FiniteNormH2Vanishing.{u,v}` is a
Prop-valued statement definition. For arbitrary fields `K : Type v` and
`L : Type u` in independent universes, equipped with `Algebra K L`, it states:
if `L/K` is finite Galois and the determinant norm

\[
N_{L/E}: L^\times \longrightarrow E^\times
\]

is surjective for every `E : IntermediateField K L`, then
`Subsingleton (relativeCohomology K L 2)`. The declaration specifies this
implication; this module supplies no proof of it.

## Exact objects and quantifiers

The norm is the existing `Langlands.LocalClassField.normUnits E L`, defined
as `Units.map (Algebra.norm E)`. Each intermediate field carries its actual
subfield structure and its canonical inclusion into `L`; no alternative scalar
actions are quantified. The local `FiniteDimensional E L` instance is
`FiniteDimensional.right K E L`, obtained from the finite extension `L/K`
and its canonical scalar tower. It adds no hypothesis. Although `E/K` need
not be normal, `L/E` is finite Galois.

The norm family includes every intermediate field, including the bottom
(the image of `K`) and the top (`L`). In particular, it includes the fixed
field of every subgroup of `Gal(L/K)`, not only those of normal subgroups.
This full family provides the subgroup norm conditions in the source
argument. Surjectivity of the single norm `Lˣ → Kˣ` is not the antecedent.

The conclusion uses the underlying carrier of the existing Mathlib ordinary
group cohomology module:

```lean
relativeCohomology K L 2 = groupCohomology (unitsRepresentation K L) 2
```

Here `unitsRepresentation K L` has underlying module `Additive Lˣ`, with
the actual Galois action and scalar ring `IntegerScalars.{u} = ULift.{u} ℤ`.
The universe lift changes the scalar presentation, not the field, its units,
or its automorphism group. The subsingleton assertion says that this actual
second cohomology group vanishes. The field, algebra, finite-dimensionality,
Galois, and displayed norm-family assumptions are the entire antecedent.
In particular there is no additional cohomological vanishing assumption.

## Source and derived scope

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, Graduate Texts in Mathematics 67, Springer, 1979, registered as
`serre-1979-local-fields`; retained original:
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
The relevant locations are Chapter X, Section 7, Proposition 11 and its
proof, printed pages 161–162 (PDF pages 167–168), and Chapter IX, Section 5,
Theorem 8, printed page 145 (PDF page 151).

This statement is the finite-extension consequence of the proof of
Proposition 11, rather than that proposition's field-wide equivalence.
Fix the single finite Galois extension `L/K` and a subgroup `H` of its
Galois group. The fixed field `E = L^H` belongs to the quantified family.
Surjectivity of `N_{L/E}` gives vanishing of degree-zero Tate cohomology
for `H` acting on `Lˣ`. Hilbert 90 gives degree-one vanishing for the same
subgroup. Thus the two-consecutive-degree criterion of Chapter IX,
Theorem 8 applies (in particular to the Sylow subgroups), yielding
cohomological triviality and hence ordinary degree-two vanishing for
`Gal(L/K)`. This explains the derived formulation; it is not a Lean proof
in this module. Neither a Brauer-group comparison nor a hypothesis about
all finite extensions of `K` is required by this formulation.

Worker 84 authored the Lean/Markdown pair following the statement and source
localization specified by Worker 37.
