# The Frobenius-twisted strong map does not extend to `F₄`

`NonExtensionStatement` is the statement that the strong atlas map `weakMap`
over `F₂` (module `GroundFieldExtensionCounterexample/WeakMap`) has no ground
field extension to `F₄` that keeps its pullbacks. The declaration is in the
namespace `Langlands.Analytic.GroundFieldExtensionCounterexample`.

## Provenance

The project operator asked for this statement in Task 7100: "Put your
counterexample into the Library as a theorem with its Markdown (K = F2 with the
trivial norm, L = F = F4, the two incomparable triple charts, Frobenius on one of
them): it is the reason for the restriction, and it records that a weak
StrongHom need not extend along a ground field extension." It is internal to this
project and has no literature source. It explains why item 3 of Task 7100 extends
only `CompatibleStrongHom`s along a ground field extension.

## Statement

Write `S` for `sourceAtlasPresentation` and `T` for `targetAtlasPresentation`.
Both are affinoid atlas presentations over `F₂` with the trivial norm. Write
`S_L` and `T_L` for their ground field extensions to `F₄`. These are
`IndexedAffinoidAtlas.GroundFieldExtension.presentation F₂ F₄ S.atlas` and the
same for `T`, from Task 7100 item 3. Their charts are indexed by the original
chart indices, and their chart algebras are the extended algebras
`PresentedAffinoidAlgebra.GroundFieldExtension.algebra F₂ F₄ (S.atlas.algebra i)`.

`NonExtensionStatement` says that there is no `F : StrongHom S_L T_L` with the
following property. Take any source chart `i` and target chart `j` that are
admissible for `weakMap`, meaning that `weakMap.baseMap` maps the chart `i`
into the chart `j`. Then the pair `(i, j)` is also admissible for `F`, and
`F.pullback i j` equals `PresentedAffinoidAlgebra.GroundFieldExtension.map F₂
F₄ (weakMap.pullback i j)`. That is the ground field extension of the bounded
pullback of `weakMap`.

The statement does not restrict the base map of `F`. It asks only that every
admissible pair of `weakMap` stays admissible for `F`, with the extended
pullback. This is what the item-3 construction provides for a
`CompatibleStrongHom`.

## Why it holds

This is an informal outline; the proof is a separate artifact. On the left
triple chart the pullback of `weakMap` is the factorization of `restrictMap`.
On the right triple chart it is that factorization followed by Frobenius. Over
`F₂` both induce the same map of spectra. After extension to `F₄`, the
extended Frobenius moves points of the source spectrum. The two triple charts
contain a common single-factor chart. Comparing the two extended pullbacks
there shows that `F` cannot have both of them.
