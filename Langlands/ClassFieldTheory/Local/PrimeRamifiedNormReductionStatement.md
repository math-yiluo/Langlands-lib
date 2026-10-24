# Higher-unit norms and critical representatives

Authors: Worker 27 (statement design and Markdown, shared draft revision 1)
and Worker 298 (source audit against Serre and the Library definitions,
checking and submission). This pair states
`Langlands.LocalClassField.PrimeRamifiedNormReduction.{u,v}` as a
proposition definition. It provides no proof of that proposition, and
acceptance of this statement is not a proof.

## Exact statement

Let `p` be prime and let `F : PadicField.{u} p` and
`L : PadicField.{v} p` have an actual `F.Carrier`-algebra structure on
`L.Carrier`, compatible with their `Padic p`-algebras through
`IsScalarTower (Padic p) F.Carrier L.Carrier`. Assume
`FiniteDimensional F.Carrier L.Carrier` and
`IsGalois F.Carrier L.Carrier`. Write
`ell = Module.finrank F.Carrier L.Carrier`,
`TF = F.canonicalTopologicalData`, and
`TL = L.canonicalTopologicalData`.

Assume that `ell` is prime and
`TL.ramificationIndex = ell * TF.ramificationIndex`, the canonical
absolute-index expression of total ramification. Given a natural number
`t`, assume that for every natural `i` the actual subgroup
`Ramification.Padic.lowerRamificationGroup TL F.Carrier i` is the full
automorphism group when `i ≤ t`, and the trivial group when `i > t`.
This is a condition on the existing lower filtration, not a substitute
family of subgroups.

Define the natural-number index function

```text
ψ(n) = n                         if n ≤ t,
ψ(n) = t + ell * (n - t)          if t < n.
```

For this actual single break it is the integral inverse-Herbrand formula.
This proposition uses the displayed natural formula directly; it does not
separately assert its equality with the real `herbrandPsi`.

Set `N = normUnits F.Carrier L.Carrier`, the actual determinant norm on
field units. The proposition asserts these three conclusions:

1. For every natural `n > t`,
   `(TL.unitFiltration (ψ n)).map N = TF.unitFiltration n`.
2. For every natural `n ≥ t`,
   `(TL.unitFiltration (ψ n + 1)).map N = TF.unitFiltration (n + 1)`.
3. For every `x : F.Carrierˣ` there exist `y : L.Carrierˣ` and
   `z : TF.unitFiltration t` such that
   `x = N y * (z : F.Carrierˣ)`.

The first two are subgroup image equalities. Each therefore asserts both
norm containment and a preimage at the specified level for every target
unit. The second includes `n = t`, giving exact norms on `U_F^(t+1)`.
The last conclusion supplies actual multiplicative witnesses; `x` ranges
over all nonzero field elements, without a restriction on its valuation.
It includes elements of positive and negative order.

## Existing objects and boundary cases

`Norms.lean` defines `normUnits` by `Units.map (Algebra.norm F.Carrier)`.
The finite-dimensional hypothesis ensures that this is the determinant
norm of the finite extension in question. `Units.lean` defines
`unitFiltration n` as the image of the integer-ring congruence units in the
field unit group. At level zero it is the whole integer-unit subgroup,
which is generally smaller than the field unit group.

Thus at `t = 0` the third conclusion still requires valuation reduction:
it expresses every field unit as a norm times an integer unit. For
`t > 0` the representative is a principal unit of depth `t`. No theorem
asserting that the critical graded norm itself is surjective is included.

All fields, orders and unit filtrations use the supplied fields' canonical
local data. The independent universes `u` and `v` allow the same proposition
to be used for a finite compositum over its unramified base field. The
proposition introduces no auxiliary norm map, quotient model, or
surjectivity certificate.

## Source and derived provenance

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, GTM 67, Springer (1979), registered as
`serre-1979-local-fields`. The retained original is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 27 reread the relevant pages on 2026-10-23, and Worker 298
rechecked V.3 from its setup through Corollary 7 (printed pages 83–87 /
PDF pages 90–94) on 2026-10-24. No source-specific
errata note was found in the checked project and Library notes.

Serre's base field `K` corresponds to `F` here. A prime-degree Galois
extension has cyclic Galois group, as required in his Chapter V, §3.
The residue field of a p-adic field is finite and hence perfect.

- V.3, Corollary 2 to Proposition 5, printed page 85 / PDF page 92,
  gives surjectivity of the graded norm above `t`, and below `t` when the
  residue field is perfect.
- V.3, Corollary 3, printed pages 85–86 / PDF pages 92–93, states the
  two exact higher-unit norm equalities used here. Its proof passes from
  the graded surjections to the filtered groups by completeness, invoking
  Lemma 2, and uses the norm containments for the second equality.
- V.3, Corollary 6, printed page 86 / PDF page 93, gives the unit
  quotient isomorphism below and through `t`.
- V.3, Corollary 7 and its proof, printed pages 86–87 / PDF pages
  93–94, identify the critical norm quotient with the full norm quotient.
  Part (b) uses Corollary 6 to reduce integer units; part (c) uses
  residue degree one to remove the valuation obstruction.

The first two Lean clauses are direct encodings of Corollary 3 in the
published unit subgroups. The third is a derived witness formulation:
surjectivity of `U_F^t → Fˣ / N(Lˣ)` says that the class of any `x` is the
class of some `z ∈ U_F^t`, so `x / z = N(y)` for an actual `y`.
Rearrangement in the commutative unit group gives `x = N(y) * z`.
The proposition asserts this consequence, not the full quotient
isomorphisms or the order of the norm quotient.

## Proof obligations and intended use

The separate single-break and graded-norm statements,
`Langlands.LocalClassField.PrimeTotallyRamifiedBreak` and
`Langlands.LocalClassField.PrimeRamifiedGradedNorm`, are propositions,
not proofs, and this module neither imports nor assumes them. They do not
prove any of these conclusions. A proof must establish the graded surjectivity,
complete the successive approximations in the actual local fields, and
justify valuation reduction. In particular, `unitFiltration 0` cannot be
silently substituted for `F.Carrierˣ`.

The finite bounded-base-change norm argument uses clause 3 to reduce its
given element to level `t`. After solving the critical residue equation,
clause 2 with `n = t` removes the error in level `t + 1`. This pair does
not assert existence of an unramified extension, compatibility of breaks
or coefficients after base change, or the parent norm theorem.
