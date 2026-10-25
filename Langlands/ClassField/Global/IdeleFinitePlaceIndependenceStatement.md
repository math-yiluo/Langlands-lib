# Finite idele invariant independence from the upper place

Worker 21 states the internal supporting target
`Langlands.ClassField.Global.FiniteIdeleInvariantPlaceIndependenceStatement.{u}`.
It is a `Prop`-valued definition with no parameters outside the proposition:

```lean
∀ I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p,
  (∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility) →
    FiniteIdeleInvariantPlaceIndependent I
```

The conclusion uses the published predicate from
`Langlands.ClassField.Global.IdeleFiniteInvariantTransfer`. Expanded, it says
that for every pair of number fields `F E : Type u`, every `F`-algebra
structure on `E` making `E/F` Galois, every finite place `v` of `F`,
every two finite places `w,z` of `E` lying above `v`, and every class
`c : relativeIdeleCohomology F E 2`,

```lean
finiteIdeleInvariant I v w c = finiteIdeleInvariant I v z c
```

These are the existing maps on actual idele cohomology. Each first applies
`ideleLocalMap` and then the supplied local invariant family at the
canonical p-adic package `padicField v`. The arbitrary common universe and
the arbitrary supplied family are retained. Only `InflationCompatibility`
is assumed: neither `RelativeImages`, `ArithmeticNormalization`, nor a
separate conjugacy law is a premise. In particular, the conclusion follows
under the stronger local hypotheses of `GlobalInvariantStatement`.

The provenance is internal. This target isolates the discharge of the
finite-place independence premise in `IdeleFiniteInvariantTransfer`.
Its intended derivation combines the published
`exists_finitePlaceEquiv_eq` (transitivity on places),
`ideleLocalMap_finiteCompletionConjugacy_apply` (actual localization
transport), and
`InvariantFamily.relative_relativeConjugacy_refl_of_inflationCompatibility`
(same-base naturality from inflation). Those results are in
`IdeleLocalInjectivity`, `FinitePlaceConjugacy`, and
`Langlands.ClassFieldTheory.Local.SameBaseConjugacy`, respectively.
This pair states the target; it does not contain its proof or assert
the existence of global idele-class invariant maps.
