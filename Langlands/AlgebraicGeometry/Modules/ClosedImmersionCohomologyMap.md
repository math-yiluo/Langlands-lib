# Relative cohomology maps along a closed immersion

This internal construction uses the actual module-sheaf pushforward and the
existing derived cohomology comparisons. All schemes, rings and modules have
arbitrary common universe `u`. Let `h : Z → Y` be a closed immersion,
`g : Y → Spec R`, `g' : Z → Spec S`, `φ : R → S`, and
`w : h ≫ g = g' ≫ Spec.map φ`.

For any actual module sheaf map `a : M → h_* N`,
`closedImmersionCohomologyMap φ g g' h w a n` is the `R`-linear map

```text
Hⁿ_R(Y,M) → restrictScalars φ (Hⁿ_S(Z,N)).
```

It is the cohomology map of `a`, followed by the inverse of
`pushforwardCohomologyIso`, then `relativeCohomologyBaseRingIso`.
The published closed-immersion vanishing theorem supplies the vanishing of
all positive higher direct images for the actual module `N`. Thus this
construction does not require quasi-coherence, flatness or properness.

`closedImmersionCohomologyMap_naturality` treats maps `b : M → M'`,
`c : N → N'`, `a : M → h_* N` and `a' : M' → h_* N'` satisfying
`b ≫ a' = a ≫ h_* c`. Its conclusion is

```text
Hⁿ(b) ≫ closedImmersionCohomologyMap(a') =
  closedImmersionCohomologyMap(a) ≫ restrictScalars φ (Hⁿ(c)).
```

The proof first inverts the existing naturality square for
`pushforwardComparison`, using its isomorphism. It then combines this with
naturality of the base-ring comparison and functoriality of cohomology.
This is an internal consequence of the imported constructions; it asserts
no transitivity under composition of closed immersions.
