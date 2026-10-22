# Naturality of finite-to-absolute inflation

This module states two internal comparison obligations for the actual
cohomology maps defined in `Cohomology`, `ClosureCoefficients`, and
`FiniteComparison`. Both declarations are propositions; this module proves
neither proposition.

`ClosureInflationTowerCompatibility` quantifies over a field `K` and finite
normal intermediate fields `L` and `M` of its specified algebraic closure.
The supplied `L`-algebra structure on `M` must form scalar towers both over
`K` and into that closure. Consequently the composite `L → M → Kbar`
is the actual inclusion of `L`. For every natural cohomological degree `n`
and class `x` in ordinary `H^n(Gal(L/K), Lˣ)`, the statement requires

    closureInflation K M n (relativeInflation K L M n x)
      = closureInflation K L n x.

`ClosureInflationBaseChangeCompatibility` quantifies over a finite extension
`E/K`, a specified compatible algebra structure `Kbar → Ebar`, a finite
normal intermediate field `L/K` inside `Kbar`, and a finite normal intermediate
field `M/E` inside `Ebar`. The supplied structures `K → M` and `L → M`
must form the towers `K → E → M` and `K → L → M`. An explicit hypothesis
requires, for every `a : L`,

    (M → Ebar)((L → M)(a)) = (Kbar → Ebar)((L → Kbar)(a)).

This equality binds the finite stage map to the same closure embedding used
by `absoluteRestriction`. For every `n` and ordinary relative class `x`,
the conclusion is

    absoluteRestriction K E n (closureInflation K L n x)
      = closureInflation E M n
          (relativeRestriction K E M n (relativeInflation K L M n x)).

The target of `relativeInflation K L M` is the ordinary cohomology of the
actual automorphism group `Gal(M/K)`; its definition requires `L/K` to be
normal, and does not require `M/K` to be normal. Neither `E/K` nor `M/K`
is assumed Galois. There is no unramifiedness, characteristic-zero, invariant,
or arithmetic-coordinate hypothesis. Both propositions retain arbitrary
common carrier universe `u`, every natural degree including zero, and
degree-one extensions.

The absolute cohomology is continuous cohomology of the actual absolute
Galois group with discrete closure-unit coefficients. `closureInflation`
uses the inverse of the proved finite continuous-to-ordinary comparison and
then continuous inflation. The other maps are the existing field-induced
cohomology maps, with their actual unit inclusions. No alternate cohomology
model or freely chosen comparison map occurs in either statement.

## Provenance and intended use

These are internal naturality statements for published constructions, not
translations of a new literature theorem. Their expected proof uses the
published `Langlands.Continuous.continuousToOrdinary_naturality`, functoriality
of the actual cochain maps, composition of field restrictions, and composition
of the unit inclusions. Those identifications remain proof obligations.

The tower identity will compare finite representatives when constructing
absolute local invariants. The base-change identity will transfer the
separate finite invariant degree law to absolute restriction once suitable
finite unramified stages have been constructed. These statements assert
neither the existence of such stages nor an absolute invariant theorem.

Authored by Worker 154.
