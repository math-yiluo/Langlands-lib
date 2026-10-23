# Cyclic prime-step towers for finite solvable Galois extensions

Worker 109 authored this statement and its explanation. The mathematical
provenance is the finite-group and Galois-correspondence argument underlying
Serre's reduction in *Local Fields*, Chapter V, §4, Proposition 7, printed
page 90 (PDF page 97). This module defines a proposition target; it proves
neither the tower theorem nor Serre's norm theorem.

## Exact statement

`Langlands.FieldTheory.SolvableGaloisPrimeTower.{u,v}` quantifies over fields
`K : Type u` and `L : Type v`, an algebra structure `Algebra K L`, finite
dimensionality, `IsGalois K L`, and solvability of the actual automorphism
group `Gal(L/K)`. The two universes are independent. There is no local-field,
valuation, or characteristic assumption.

The conclusion supplies one natural number `n` and one function
`T : Fin (n + 1) → IntermediateField K L`. Its first value is the bottom
intermediate field, the image of `K` in `L`; its last value is the top
intermediate field, all of `L`. For each `i : Fin n`, the statement supplies
an inclusion `h : T i.castSucc ≤ T i.succ`. Consecutive inclusions make the
whole chain ascending. The induced algebra is installed explicitly as
`(IntermediateField.inclusion h).toAlgebra`, and that same local instance
is used throughout all four assertions for this step:

- `FiniteDimensional (T i.castSucc) (T i.succ)`;
- `IsGalois (T i.castSucc) (T i.succ)`;
- `IsCyclic ((T i.succ) ≃ₐ[T i.castSucc] (T i.succ))`;
- `Nat.Prime (Module.finrank (T i.castSucc) (T i.succ))`.

Thus the fields are actual subfields of `L`, with their inherited field
structures and the literal inclusion as scalar map. The cyclic group is the
actual group of relative algebra automorphisms. Neither an abstract copy of
a field nor a certificate for existence of a tower is substituted. The
finite-dimensional assertion is explicit even though prime finrank already
forces it. Each step has degree greater than one. The representation permits
`n = 0`: there is one field, both endpoints coincide, and there are no step
conditions. This covers trivial extensions, whose bottom and top coincide.
The statement does not require each `T i` to be Galois over `K`.

## Derived mathematical provenance

For a finite solvable group `G`, take a composition series
`G = H₀ ⊇ H₁ ⊇ ⋯ ⊇ Hₙ = 1`. Each `Hᵢ₊₁` is normal in `Hᵢ`. Its
composition factor is finite, simple and solvable, hence abelian and cyclic
of prime order: a nontrivial simple solvable group has trivial commutator
subgroup, and a finite simple abelian group has prime order. Apply this to
`G = Gal(L/K)`, which is finite for the finite extension in the statement.

The finite Galois correspondence reverses the series to the ascending
fixed fields `Tᵢ = L^{Hᵢ}`. The endpoint fixed fields are bottom and top.
Normality of `Hᵢ₊₁` in `Hᵢ` makes `Tᵢ₊₁/Tᵢ` Galois; restriction identifies
its automorphism group with `Hᵢ/Hᵢ₊₁`. Its degree therefore equals the
prime order of that cyclic group. These are statements about the inclusions
of these fixed fields in the same `L`. For the trivial group, use the
length-zero series. This explains the proposed generic target; the module
contains no Lean implementation of this argument.

Serre's V.4 Proposition 7 first reduces to a finite Galois extension and then
uses a totally ramified descent whose Galois group is solvable. He reduces
the remaining norm argument to cyclic prime degree by dévissage. Our target
isolates the generic tower needed for that step. Solvability of local Galois
groups, descent, norm transitivity, norm surjectivity, and cohomological
consequences are outside this module. The generic composition-series
formulation above is a derived interface, not a claim that Serre states
these Lean quantifiers or provides a formal proof.

## Source and dependencies

- Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
  Graduate Texts in Mathematics 67, Springer, 1979; registered source
  `serre-1979-local-fields`, Chapter V, §4, Proposition 7, printed page 90,
  PDF page 97. Retained original:
  `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
  SHA256: `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
  Worker 109 read printed pages 89–90 (PDF pages 96–97); no project Serre
  errata entry was present when checked.
- The module imports Mathlib's `FieldTheory.Galois.Basic` and
  `GroupTheory.Solvable`, using their field, algebra, automorphism and
  solvability definitions. Existing Mathlib and Library files are unchanged.
