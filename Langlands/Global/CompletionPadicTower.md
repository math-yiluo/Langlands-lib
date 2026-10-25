# Canonical p-adic completion packages in number-field towers

Author: Worker 50. This is a supporting definition unit for task
`87277693-540a-40ff-828f-7cd5c591f823`.

## Scope and provenance

This module is an internal coherence construction derived from the published
`Langlands.Global.CompletionPadic` packages, the published
`Langlands.ClassField.Global.CompletionTower.completionMap_comp`, and Mathlib's
contraction of ideals in algebra towers. It adds no arithmetic objects or
assumptions beyond those interfaces. No new original-source claim is made.

Fix number fields `F K : Type u`, an algebra `Algebra F K`, finite places
`v : HeightOneSpectrum (𝓞 F)` and `w : HeightOneSpectrum (𝓞 K)`, and
`w.asIdeal.LiesOver v.asIdeal`. The universe `u` is arbitrary. No normality or
Galois hypothesis on `K/F` is needed. The upper completion remains the actual
`w.adicCompletion K`, with the existing completion embedding from
`v.adicCompletion F`.

All declarations below are in namespace `Langlands.Global.CompletionPadic`.
The module adds a new pair and leaves all existing modules unchanged. It does
not prove finite invariant restriction or a global summation formula.

## Transport while retaining the carrier

For any natural number `p` with `Fact p.Prime` and equality
`h : residuePrime w = p`:

- `padicMapAt w h` transports the domain index of `padicMap w` to give a ring
  homomorphism `Padic p →+* w.adicCompletion K`.
- `padicAlgebraAt w h` is the algebra induced by this map. Like `padicAlgebra`,
  it is an instance-reducible definition, not a global instance.
- `padicFieldAt w h : PadicField p` has carrier definitionally equal to
  `w.adicCompletion K`, its existing field instance, algebra
  `padicAlgebraAt w h`, and the transported finite-dimensionality certificate
  `padicFinite w`.
- `padicAlgebraAt_heq` and `padicFieldAt_heq` express heterogeneous equality to
  the original canonical algebra and package. Heterogeneous equality is used
  because the scalar prime indices can differ syntactically. After eliminating
  `h`, these are reflexive equalities, including the algebra data.

Each transport is implemented by equality induction on `h`. The carrier and
field structure are not transported, so consumers use ordinary equality of
maps on the actual completion and need no cast on cohomology classes.

`absolute_padicFieldAt` and `relative_padicFieldAt` apply to every family

```lean
I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u,t} p
```

with arbitrary extension universe `t`. They assert equality of the additive
homomorphisms obtained from `I p` at `padicFieldAt w h` and from
`I (residuePrime w)` at `padicField w`. For the relative comparison, an
extension `L : Type t` carries a field structure, the specified algebra over
`w.adicCompletion K`, finite dimensionality, and a Galois certificate, exactly
as required by `InvariantFamily.relative`. Both comparisons follow by equality
induction and reflexivity. They assume no restriction, naturality, or
isomorphism-invariance law for `I`.

## Compatibility in the number-field tower

`rationalPlace_eq v w` proves

```lean
rationalPlace w = rationalPlace v
```

by composing `LiesOver` from `w` to `v` and from `v` to its rational
contraction. `Ideal.over_def` identifies the contracted ideals, and
`HeightOneSpectrum.ext` identifies the places. Applying the natural-number
value of `Rat.HeightOneSpectrum.primesEquiv` gives
`residuePrime_eq v w : residuePrime w = residuePrime v`.

`towerPadicField v w` abbreviates
`padicFieldAt w (residuePrime_eq v w)`. It packages the actual upper completion
over `Padic (residuePrime v)`. `towerPadicField_heq` records its heterogeneous
equality to `padicField w`.

The map comparison is

```lean
completionMap_comp_padicMap v w :
  (FiniteExtension.completionMap v w).comp (padicMap v) =
    padicMapAt w (residuePrime_eq v w)
```

The helper `padicMapAt_eq_of_rationalPlace_eq` computes the transported map
using any equal rational place `q`. Its proof eliminates the equality of
places. For `q = rationalPlace v`, the comparison therefore reduces to
associativity of ring-homomorphism composition and the already published
`CompletionTower.completionMap_comp` for `ℚ → F → K`.

`towerPadicField_isScalarTower v w` supplies

```lean
letI := (padicField v).algebra
letI := (towerPadicField v w).algebra
IsScalarTower (Padic (residuePrime v))
  (v.adicCompletion F) (w.adicCompletion K)
```

The intermediate-to-upper algebra is the existing scoped
`FiniteExtension` completion algebra. The proof applies
`IsScalarTower.of_algebraMap_eq` to the preceding equality of ring
homomorphisms. Thus the tower uses the canonical p-adic maps and the existing
completion map; it does not choose a merely isomorphic algebra.

Finally, `absolute_towerPadicField` and `relative_towerPadicField` specialize
the arbitrary-family transport comparisons to this tower. In particular,

```lean
(I (residuePrime v)).relative (towerPadicField v w) L =
  (I (residuePrime w)).relative (padicField w) L
```

as maps on the same relative cohomology group.

## Consumer usage and validation

A consumer can install `(padicField v).algebra`,
`(towerPadicField v w).algebra`, and `towerPadicField_isScalarTower v w`
locally. The existing `FiniteExtension.local_finite v w` supplies finite
dimensionality over the lower completion. Both packages can then be supplied
to the local `InvariantFamily.RelativeRestriction` predicate at
`residuePrime v`, and `relative_towerPadicField` rewrites the upper invariant
to the original canonical package at `residuePrime w`.

A private compilation check exercised precisely this usage with a general
finite Galois extension of the completions and an arbitrary family satisfying
the existing relative-restriction predicate. This check is an interface test;
no global invariant-restriction theorem is included in the contribution.
The new module and the usage check compiled without warnings. Inspection of
`towerPadicField_isScalarTower` reported only `propext`, `Classical.choice`,
and `Quot.sound`. Development checks are not independent acceptance.
