# Regular algebraicity of a weak cyclic descent at a conjugate pair: proof

`Langlands.Automorphic.Unramified.cyclicWeakBaseChangeRegularAlgebraicTC` proves
[`CyclicWeakBaseChangeRegularAlgebraicTCStatement`](CyclicWeakBaseChangeRegularAlgebraicStatement.md)
at the independent universes `uK`, `uE` of the two fields and `uV`, `uW` of the
supercuspidal carriers. Its premises are restricted B7
(`RestrictedCyclicWeakBaseChangeComplexPlaceStatement`, used through its first,
base-change clause) and the totally complex bridge
`CuspidalComplexParameterBridgeTCStatement` at `uK` and at `uE`. The proof uses the
hypotheses at the conjugate pair `v₀`, `c(v₀)`, the unique places `w₀`, `wc` above
them, the unitary central characters and the supercuspidal components only to apply
restricted B7.

## The proof

1. `K` is totally complex, an instance of every CM field, and `E` is totally complex
   by Mathlib's `NumberField.isTotallyComplex_of_algebra K E`.
2. Upstairs parameters. The existence clause of the bridge over `E` gives, by choice,
   a list `dsT w` with `T.realization.HasComplexPlaceParameter w (dsT w)` at every
   complex place `w` of `E`. The second clause gives a character `θ` of the enveloping
   center matching `dsT`, which acts on `T` by scalars. Regular algebraicity of `T`
   (`CuspidalOperatorRealization.isoClass_isRegularAlgebraic_iff`) gives a regular
   algebraic character `χ` acting on `T` by scalars. The carrier of `T` is nontrivial,
   so `OperatorRealization.HasInfinitesimalCharacter.unique` gives `θ = χ`. The third
   clause of the bridge then makes every list `dsT w` Clozel regular algebraic of
   rank `r + 1` (`ComplexPlaceParameter.IsClozelRegularAlgebraic`).
3. Downstairs lists. For every complex place `v` of `K`, choose a place `wv v` of `E`
   above it (`Langlands.Global.AdelicFunctoriality.exists_infinitePlace_above`, from Mathlib's
   `NumberField.InfinitePlace.comap_surjective`) and set
   `dsS v = complexPlaceParameterTransport v (wv v) (dsT (complexPlaceAbove v (wv v)))`.
   The transport is involutive (`complexPlaceParameterTransport_involutive`), so its
   value at `dsS v` is the list `dsT (complexPlaceAbove v (wv v))`, a parameter of `T`.
   The base-change clause of restricted B7, applied to `S`, `T`, `v`, `wv v` and
   `dsS v`, then says that `dsS v` is a parameter of `S` at `v`.
4. Downstairs infinitesimal character. The second clause of the bridge over `K` gives a
   character `ψ` matching `dsS` that acts on `S` by scalars. Every `dsS v` is Clozel
   regular algebraic by `isClozelRegularAlgebraic_complexPlaceParameterTransport`, so
   the third clause of the bridge over `K` makes `ψ` regular algebraic, and `S` is
   regular algebraic.

## The auxiliary results

- `isClozelRegularAlgebraic_complexPlaceParameterTransport`: transport preserves
  `IsClozelRegularAlgebraic n`. The transport is the identity or maps
  `ComplexCharacterData.conj` over the list. Conjugation negates the weight and keeps
  the exponent, so it interchanges `zExponent` and `zBarExponent`. The two integrality
  witnesses `p`, `q` are interchanged, and the two `Nodup` conditions are
  interchanged.
- `Langlands.Global.AdelicFunctoriality.exists_infinitePlace_above`: every infinite place of `F` has a place of `E`
  above it, for an arbitrary extension of number fields `E/F`.

## Source

This is the archimedean step of the proof of Harris (1998), Lemma 1.6, pp. 188–189
(source ID `harris-1998-local-langlands`, TeX lines 750–754): the descent `π` lies in
`Reg(n, E)` because its base change `π^u` lies in `Reg(n, E^u)` and `π_w ≅ π_{w^u}` at
every complex place `w` and every place `w^u` above it. In the Lean statement the
descent is `S` over `K` and the base change is `T` over `E`. Restricted B7 supplies the
comparison of the local components at the complex places, in the selected coordinates,
and the bridge supplies the passage between these components and the infinitesimal
characters.
