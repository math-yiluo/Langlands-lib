# Prime inertia: the actual break pattern

This module defines the proposition
`Langlands.LocalClassField.PrimeInertiaBreakPattern.{u,v}`. It is a derived
conditional support statement about the existing ramification constructions.
The module contains no proof of the proposition.

## Complete interface

For every natural prime `p`, with `[Fact p.Prime]`, take
`F : PadicField.{u} p` and `L : PadicField.{v} p` in independent arbitrary
universes. The extension retains the supplied
`Algebra F.Carrier L.Carrier`, compatible
`IsScalarTower (Padic p) F.Carrier L.Carrier`,
`FiniteDimensional F.Carrier L.Carrier`, and
`IsGalois F.Carrier L.Carrier` instances. The proposition quantifies every
supplied `T : L.TopologicalData`; it does not select canonical topological
data or replace the supplied scalar structures.

Let `ell = Module.finrank F.Carrier L.Carrier`. The hypotheses are
`Nat.Prime ell` and `Ramification.Padic.inertia T F.Carrier = ⊤`.
Inertia is the kernel of the actual action of the base-field automorphisms
on the residue field attached to `T`. The conclusion gives a single
`t : ℕ` satisfying all three assertions:

1. For every natural index `i`,
   `Ramification.Padic.lowerRamificationGroup T F.Carrier i` is `⊤` when
   `i ≤ t` and `⊥` otherwise. These are subgroups of the actual group
   `L.Carrier ≃ₐ[F.Carrier] L.Carrier`. The lower group uses displacement
   of every integer-ring element modulo the `(i + 1)`st maximal-ideal power.
2. `0 < t` holds exactly when the actual lower group at index `1` is `⊤`.
3. For every natural `n`, the existing real function
   `Ramification.Padic.herbrandPsi T F.Carrier` at `(n : ℝ)` equals the
   real cast of the natural expression
   `if n ≤ t then n else t + ell * (n - t)`.

Natural subtraction is used only in the second branch, where `t < n`.
The case `t = 0` is retained. At `n = t` the first branch is selected;
both expressions give `t`. The formula is asserted only at natural inputs.
The existing `herbrandPsi` is the inverse of the order isomorphism built
from actual lower-group orders in `Herbrand.Finite`.

## Derived provenance and proof boundary

The structural argument uses Galois cardinality equal to extension degree,
prime-order subgroup dichotomy, the equality of the zeroth lower group with
inertia, antitonicity, and eventual triviality. The break is one less than
the first trivial index. The group orders are `ell` through that break and
one afterwards. Finite sums in `herbrandPhi_floor` then evaluate the actual
Herbrand function at the two candidate inverse arguments; the constructed
inverse identity gives the stated `herbrandPsi` formula.

The current Library already provides this route in Worker 96's
`Langlands.ClassFieldTheory.Local.PrimeInertiaBreakSupport`, through
`Langlands.LocalClassField.exists_prime_lowerRamificationGroup_pattern`
and `Langlands.LocalClassField.herbrandPsi_nat_of_prime_pattern`.
These existing helper theorems can be reused by a separate proof of the
named proposition after its publication. This statement module imports
only `Langlands.LocalFactor.Ramification.Herbrand.Finite` and
`Mathlib.FieldTheory.Galois.Basic`; it adds no arithmetic data or proofs.

Serre's arithmetic conclusion concerns a totally ramified cyclic extension
of prime degree and identifies positivity of the break with degree equal
to residue characteristic. This support proposition assumes full actual
inertia and characterizes positivity by the actual first lower group.
It neither asserts `ell = p` nor encodes total ramification by an index
identity. The arithmetic implications belong to the separate parent result
`PrimeTotallyRamifiedBreak`, proved by `primeTotallyRamifiedBreak` in
`Langlands.ClassFieldTheory.Local.PrimeRamificationBreakProof`. That parent
retains its original arithmetic hypotheses. This module does not change
its target or imports and has no dependency on a norm theorem, reciprocity,
or an unproved Herbrand compatibility statement.

## Original sources and conventions

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer (1979), registered as `serre-1979-local-fields`:
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

- IV.1, Lemma 1 and Proposition 1, printed pp.61–62 / PDF pp.68–69,
  give the actual congruence definition, decreasing filtration, zeroth
  inertia group, and eventual triviality.
- IV.3, printed pp.73–74 / PDF pp.80–81, gives real lower indexing by
  ceiling, the group-order finite-sum formula for `phi`, and its inverse
  `psi`. The imported constructions use those conventions.
- V.3 opening, printed p.83 / PDF p.90, gives the prime single-break
  pattern and displayed inverse formula. Both branches agree at the break.
  The conditional formulation here isolates the structural portion of
  that arithmetic result. IV.2 Proposition 7 and Corollaries 1 and 3,
  printed pp.67–68 / PDF pp.74–75, concern the tame quotient and wild
  group underlying the additional arithmetic positivity criterion, which
  is outside this support statement.

The registered `serre-book-corrections-2019`, Jean-Pierre Serre,
*Corrections to J-P. Serre's books* (2019), is retained at
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA256 `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`.
Its complete *Local Fields* entries on PDF pp.2–3 contain corrections to
phi glyphs on printed pp.74–75 and no correction to printed p.83.
Worker 22 read the listed original passages and corrections, verified both
fingerprints, and visually checked the displayed formula on PDF p.90.
No separate project errata note for this source was present in the checked
Library or project notes.

Worker 96 specified this conditional support interface and authored the
existing helper proof route. Worker 22 authored this proposition module
and its documentation, checked the sources, and prepared the submission.
