# Central and isomorphism comparisons for actual root-datum isogenies

This internal module is derived from the published root pullback theorem for
central isogenies, reduced-root-system lemmas, the central-isogeny
self-centralizing restriction criterion, and detection of split-torus
isomorphisms on actual characters. No new source convention is introduced.

For an isogeny `f : RootDatumIsogeny p P Q` of finite reduced integral root
data, `isCentral_iff_mapsTo_roots` says that all its root factors are one
exactly when its weight map sends every root of `P` to a root of `Q`.
Centrality gives the forward implication directly from the defining root
equation. Conversely, each image root is a positive natural multiple of a
root. Reducedness excludes such multiples of size at least two by the
published `nsmul_notMem_range_root` lemma. The target lattice is torsion free
because the perfect pairing makes it reflexive over the integers. Positivity
of every root factor then forces it to be one.

Now fix affine groups locally of finite type over an arbitrary field,
split tori `T`, `T'`, actual root data `P`, `Q` for `i : T → G`,
`i' : T' → H`, and a commuting square with `φ : G → H` and `t : T → T'`.
Assume the torus map is an actual isogeny, meaning finite, flat, and
surjective. If `φ` is a central isogeny, then
`IsCentralIsogeny.isCentral_rootDatumIsogeny` proves that every supplied
`f : RootDatumIsogeny p Q P` whose weight map is the actual character
pullback of `t` is central. The published
`roots_bijOn_of_torusRestriction` theorem sends each actual target root to
an actual source root. The algebraic characterization above therefore
applies. This argument neither chooses a new root correspondence nor
requires the supplied correspondence to coincide with a previously chosen
one. It places no extra assumption on the coweight map.

The definition `IsCentralIsogeny.rootDatumHomOfActualIsogeny` uses this
centrality result and the published `RootDatumIsogeny.toHom` adapter to
recover an exact `RootPairing.Hom Q P` from the supplied `f`. Its
specification states that both lattice maps and the root index equivalence
are definitionally those of `f`. Thus if the coweight map of `f` is the
actual cocharacter pushforward, the recovered morphism retains it too.
The root index types may lie in independent universes. Module finiteness of
the four lattices is explicit, as already required to type `f`; in the
split-torus application it follows from splitness.

The final theorem
`isIso_iff_central_bijective_rootDatumIsogeny` assumes that `i` is a maximal
torus, `i'` is a closed torus inclusion, the source torus is
self-centralizing, both tori are split, and the square commutes. Given a
supplied `f` with actual character pullback and a supplied equivalence
`IsCentralIsogeny φ ↔ f.IsCentral`, it proves

```text
IsIso φ ↔ f.IsCentral ∧ Function.Bijective f.weightMap.
```

Bijectivity of this weight map is exactly invertibility of `t` by the
published split-torus character criterion. An ambient isomorphism is a
central isogeny and induces an isomorphism on the specified maximal-torus
restriction. Conversely, the supplied centrality equivalence gives
centrality of `φ`, and the self-centralizing restriction criterion upgrades
invertibility of `t` to invertibility of `φ`. That criterion uses the full
scheme-theoretic kernel on every test scheme. Centrality is retained as a
conjunct in the conclusion.

This is a focused partial module for `IsogenyRootDatumStatement`. It proves
the forward centrality implication for a supplied actual-map root-datum
isogeny and reduces the isomorphism comparison to the centrality comparison.
It does not produce the root factors or prove the reverse implication from
root-datum centrality to centrality of the full ambient kernel. The
arbitrary field and possibly nonsmooth kernels are retained throughout.
