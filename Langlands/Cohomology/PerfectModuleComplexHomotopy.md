# Homotopy and scalar extension of perfect representatives

Author: Worker 413.

This internal helper module constructs comparisons for strictly perfect
representatives using the unchanged vocabulary of
`Langlands.Cohomology.PerfectModuleComplex`. The rings and module carriers
have arbitrary universe `u`. Derived categories use Mathlib's standard
instance, with morphisms in universe `u+1`.

`isKProjective_of_isStrictlyPerfect` uses the upper bound on a strictly perfect
complex and the projectivity of every term to apply
`CochainComplex.isKProjective_of_projective`. The finite-generation and lower
bound assumptions are not needed by that Mathlib result, but are already part
of the supplied predicate.

`homotopyEquivOfDerivedIso` takes two strictly perfect representatives and an
actual isomorphism of their images under `DerivedCategory.Q`. After using the
natural isomorphism `DerivedCategory.quotientCompQhIso`, the proof applies
`CochainComplex.IsKProjective.Qh_map_bijective` to lift both directions to the
homotopy category. Injectivity of those maps proves the inverse equations.
`HomotopyCategory.homotopyEquivOfIso` then constructs a homotopy equivalence of
the original complexes. The existential choices are made classically.

The instance `extendScalars_additive` proves additivity of
`ModuleCat.extendScalars` directly: the maps agree on tensors of the form
`1 ⊗ m` because tensoring preserves addition in the second factor.
`baseChangeHomotopyEquiv` then applies `Functor.mapHomotopyEquiv` to this
additive functor. It constructs an actual homotopy equivalence between the
ordinary scalar extensions along any homomorphism of commutative rings.

`derivedIsoOfHomotopyEquiv` uses the fact that the forward map of a homotopy
equivalence is a quasi-isomorphism, hence its image under `DerivedCategory.Q`
is invertible. The main construction, `baseChangeDerivedIso`, combines these
steps. For strictly perfect `K` and `L` over `R` with isomorphic derived
images, and any `φ : R →+* S`, it constructs an actual isomorphism

```text
Q.obj ((baseChange φ).obj K) ≅ Q.obj ((baseChange φ).obj L).
```

These constructions are internal support for the local minimal perfect
representative task, derived from Mathlib's homotopy and derived-category APIs.
They establish independence of a strictly perfect representative under
ordinary scalar extension. They construct no derived tensor functor on
arbitrary complexes and no local minimal model or descent. In particular,
their justification uses K-projectivity and actual homotopies; the
representative comparison does not follow from the definition of `baseChange`
alone.
