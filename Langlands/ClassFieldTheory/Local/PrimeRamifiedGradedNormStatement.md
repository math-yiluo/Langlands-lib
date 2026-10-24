# Prime ramified graded norm formulas

Worker 27 authored the statement design and initial documentation; Worker 96
checked the source correspondence and prepared this module for submission.
The module defines the proposition
`Langlands.LocalClassField.PrimeRamifiedGradedNorm.{u,v}` and does not
prove its norm containments or formulas.

The fields `F : PadicField.{u} p` and `L : PadicField.{v} p` have arbitrary
universes and share a prime `p`. The proposition quantifies their actual
extension algebra, its compatible scalar tower from `Padic p`, finite
dimension and Galoisness. Put `ell = Module.finrank F.Carrier L.Carrier`,
`TF = F.canonicalTopologicalData`, and `TL = L.canonicalTopologicalData`.
The arithmetic hypotheses say that `ell` is prime and
`TL.ramificationIndex = ell * TF.ramificationIndex`.

A natural number `t` is supplied with the explicit condition that the
actual `Ramification.Padic.lowerRamificationGroup TL F.Carrier i` is top
for `i ≤ t` and bottom otherwise. No norm or trace conclusion is assumed.
The local expression

```text
ψ(n) = if n ≤ t then n else t + ell * (n - t)
```

uses natural subtraction only when `t < n`. The separate statement
`PrimeTotallyRamifiedBreak` is intended to provide this actual break and
identify these integer indices with the existing real inverse Herbrand
function. The present module does not import or assume a proof of that
global statement. Its break premise is an explicit property of the
published ramification groups.

## Containments and the zero-level formula

Let `r : TF.ResidueField →+* TL.ResidueField` be the actual
`relativeResidueMap TF TL`, induced by `algebraMap F.Carrier L.Carrier`
through the integer rings. Let `N = normUnits F.Carrier L.Carrier`.
This is the determinant norm on field units. The first conclusion asserts
that `r` is bijective, expressing residue degree one.

For every natural `n`, the next two conclusions assert

```text
N(U_L^(ψ(n))) ⊆ U_F^n,
N(U_L^(ψ(n)+1)) ⊆ U_F^(n+1),
```

where every group is the published `unitFiltration`. These containments
give the actual induced map between the successive quotients already
constructed as `GradedUnits`; no arbitrary homomorphism is substituted.
The denominator in the first source quotient is at `ψ(n)+1`, not at
`ψ(n+1)`.

For `x : U_L^0` and `y : U_F^0` whose underlying field units satisfy
`y = N(x)`, the zero-level formula is

```text
Units.map r (TF.zeroUnitCoordinate y) = (TL.zeroUnitCoordinate x)^ell.
```

Here `Units.map` uses `r.toMonoidHom`. The existing zero coordinate is
reduction of the actual integer unit and takes no uniformizer.
The norm containment guarantees an appropriate `y` exists for every `x`;
the equality premise only identifies its underlying unit. It is not an
extra arithmetic assumption.

## Positive coordinates and coefficient provenance

Fix any `πF : F.Carrier` and `πL : L.Carrier` with canonical order one.
The quantification covers every such pair. Define notation in this
paragraph only:

```text
cF(n,y) = TF.residue (TF.unitCoefficient πF hF n y),
cL(m,x) = TL.residue (TL.unitCoefficient πL hL m x).
```

The published `unitCoefficient` has literal field value `(x-1)/π^m`,
with integrality proved by its construction. At a positive level its
residue is exactly the additive value of `positiveUnitCoordinate` and
of the corresponding `gradedUnitsPositiveEquiv` on a projected class.
Using this residue expression avoids casts between differently indexed
subtypes without changing the coordinate map.

Each clause quantifies every actual source and target filtration element
at the indicated levels, subject to `y = N(x)` as field units.

- If `0 < n < t`, an integer `a` has exact field value
  `Algebra.norm F.Carrier πL ^ n / πF^n`, its residue is nonzero, and
  `r(cF(n,y)) = r(TF.residue a) * cL(n,x)^p`.
- If `0 < t`, integers `a` and `b` have exact field values
  `Algebra.norm F.Carrier πL ^ t / πF^t` and
  `Algebra.trace F.Carrier L.Carrier (πL^t) / πF^t`.
  Both residues are nonzero, and the formula is
  `r(cF(t,y)) = r(TF.residue a) * cL(t,x)^p +
  r(TF.residue b) * cL(t,x)`.
- If `t < n`, an integer `b` has exact field value
  `Algebra.trace F.Carrier L.Carrier (πL^(ψ(n))) / πF^n`,
  its residue is nonzero, and
  `r(cF(n,y)) = r(TF.residue b) * cL(ψ(n),x)`.

The norm in the first two coefficients is raised to the indicated power
after applying the norm. The integer witnesses assert integrality of the
specified quotients, and their coercion equalities fix their values
uniquely. They do not provide coefficients chosen merely to fit the
residue-field function.

All equalities are written in `TL.ResidueField` after applying the
forward scalar-induced map `r`. Its asserted bijectivity recovers the
usual description over `TF.ResidueField`, while the formulas keep the
actual identification visible. For the first and second positive cases,
the actual break is positive and hence `ell = p`; establishing this fact
is part of the arithmetic needed to prove the statement.

The containments and coefficient formulas are the entire conclusion.
The statement does not claim kernel sizes, completeness, norm
surjectivity on higher units, reduction of arbitrary valuations, or
unramified compatibility. Explicit trace/norm coefficients and arbitrary
supplied uniformizers are retained for a later compatibility theorem;
no polynomial identity is inferred merely from agreement of functions
on a finite residue field.

## Source and derived formulation

Jean-Pierre Serre, *Local Fields*, Marvin Jay Greenberg translation,
GTM 67, Springer, 1979, registered as `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Chapter V, §3, printed pp.83–85 / PDF pp.90–92 gives the break and index
formula, Proposition 4's two containments, and Proposition 5's four
coordinate cases. The calculation on printed p.85 gives the displayed
norm coefficient below the break and the norm and trace coefficients
at the break. Above the break it identifies the linear map with trace;
evaluating on the representative `πL^(ψ(n))` gives the displayed
coefficient for the supplied uniformizers. This last explicit quotient
and the forward-map formulation are derived expressions of that
calculation, not separately quoted source statements.

Chapter V, §4, printed pp.87–88 / PDF pp.94–95 motivates retaining the
same uniformizers and trace/norm expressions under unramified base
change. That compatibility is outside this statement. The entire cited
passage was read. The registered author corrections, *Corrections to J-P.
Serre’s books* (2019), `serre-book-corrections-2019`, PDF pp.2–3, were
also checked. They contain no corrections to printed pp.83–88; the nearby
corrections on pp.74–75 distinguish the Herbrand-function symbols. No
additional source-specific errata note was found in project notes or the
current Library.

Serre's cyclic prime-degree setting is expressed here by prime degree
and Galoisness, since the finite Galois group is then cyclic. Canonical
p-adic realizations, the exact norm on units, literal integral
coefficients, actual residue maps, and the representative-level encoding
are the derived Lean formulation. Independent proofs still need the
ramification, different/trace and norm-expansion arithmetic underlying
these conclusions; published coordinate constructions alone do not
provide it.

## Validation scope

The target is a closed proposition definition with independent universe
parameters `u` and `v`. Compilation and declaration inspection check its
elaboration and type; they supply no proof of the asserted arithmetic.
