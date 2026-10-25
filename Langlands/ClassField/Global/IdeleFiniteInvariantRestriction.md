# Finite idele invariant restriction from the local restriction law

Worker 21 proves the supporting target
`Langlands.ClassField.Global.FiniteIdeleInvariantRestrictionStatement.{u}`.
The complete unapplied type of the exported theorem is

```lean
Langlands.ClassField.Global.finiteIdeleInvariantRestrictionStatement.{u} :
  Langlands.ClassField.Global.FiniteIdeleInvariantRestrictionStatement.{u}
```

There are no parameters or hypotheses outside this proposition. It
quantifies every supplied local family
`I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p` and requires only
`hRes : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeRestriction`.
The conclusion is the existing `FiniteIdeleInvariantRestriction I`.
For every tower of number fields `F → K → E` in `Type u`, with `E/F`
Galois, and finite places `v`, `w`, and `q` with the three lying-over
relations, restriction of an actual degree-two idele-cohomology class
satisfies

```lean
finiteIdeleInvariant I w q (relativeIdeleRestriction F K E 2 c) =
  Module.finrank (v.adicCompletion F) (w.adicCompletion K) •
    finiteIdeleInvariant I v q c
```

The intermediate extension `K/F` need not be normal. The completed
degree and both localizations use the existing actual completion
algebras, and both sides use the same top place `q`. Finite-place
independence, relative images, inflation compatibility, arithmetic
normalization, and a separate naturality law are absent from this
coordinate theorem's hypotheses.

## Implemented proof

The helper `finiteIdeleInvariantRestriction_of_relativeRestriction I hRes`
introduces the number-field tower, places, and idele class. It derives
`IsGalois K E` from the given `IsGalois F E`, and installs the published
Galois and finite-dimensionality facts for the relevant completed
extensions.

It uses `padicField v` for the lower p-adic field and
`towerPadicField v w` for the intermediate one. Both are indexed by
`residuePrime v`; their carriers and field structures are definitionally
the actual completions at `v` and `w`. It installs their p-adic algebras
and the published `towerPadicField_isScalarTower v w`. The existing
`CompletionTower.isScalarTower_completion` provides the completed
three-field tower. These instances meet the hypotheses of
`hRes (residuePrime v)` without a normality hypothesis on `K/F`.

Applying that law to the top completion `q.adicCompletion E` and the
localized class `ideleLocalMap v q 2 c` gives the local restriction
formula. The theorem `relative_towerPadicField v w I` rewrites the
transported intermediate invariant as the original canonical invariant
at `w`. This equality holds for arbitrary `I` by transport of the
residue-prime index, so no additional invariance premise is introduced.

The goal is then expressed using the defining local invariant after
localization. The published identity
`ideleLocalMap_relativeIdeleRestriction v w q` rewrites the localized
global restriction as the actual local restriction. The equality
already supplied by `hRes` is exactly the resulting goal. The exported
target theorem introduces `I` and `hRes` and applies this helper.

## Consequence for the total family

`totalIdeleInvariantMaps_restriction_of_localLaws I hRes hInf hI`
additionally assumes
`hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility` and
`hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages`.
Its conclusion is
`(totalIdeleInvariantMaps I hI).RestrictionCompatible`.
Thus, in every compatible number-field tower `F → K → E` with
`E/F` Galois, the total invariant after `relativeIdeleRestriction`
equals `Module.finrank F K` times the original total invariant.

This corollary applies the existing total-family restriction theorem,
using finite-place independence derived from `hInf` and the new
coordinate restriction theorem derived from `hRes`. Both finite
coordinate premises are therefore discharged. Relative images remain
necessary to construct the finite-support sum. The existing total-family
theorem incorporates the archimedean restriction law and the finite
local-degree sum. This unit does not construct global idele-class
invariants and does not prove `GlobalInvariantStatement`.

## Provenance and checks

This is an internal derivation from the supplied local restriction law,
the published canonical p-adic tower coherence, the actual localization
restriction square, and the existing total-family consequence. The
implemented proof is described above; no new assertion from external
literature is made. All statement and imported pairs remain unchanged.

The complete entry module passed a development Lake build with zero
errors and warnings. Inspection of the target theorem reported the
sole universe parameter `u` and only `propext`, `Classical.choice`,
and `Quot.sound`. Development compilation is distinct from independent
semantic acceptance, exact-target validation, and Library publication.
