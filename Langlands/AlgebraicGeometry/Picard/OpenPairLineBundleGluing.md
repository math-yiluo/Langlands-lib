# Binary gluing of actual line bundles on an open union

This is a derived construction from the compatible-pair module in
`OpenPairModuleGluing` and the local rank-one argument
`IsLocallyFreeRankOne.exists_of_pullback`. The geometric factorizations use
Mathlib's universal property of open immersions. No new literature claim is
needed for this specialization of the Library constructions.

In `OpenPairLineBundleGluing`, let `f : Y ⟶ X` and `g : Z ⟶ X` be open
immersions, and let `L` and `K` be actual Library line bundles on the two
sources. An isomorphism `φ` between their actual module pullbacks on
`Y ×_X Z` gives the compatible-pair module on `X`. If every point of `X`
lies in the image of `f` or `g`, `glued_rankOne` proves that module locally
free of rank one: at an image point it uses the appropriate actual pullback
comparison and transports a trivialization along the open immersion.
Consequently `glue` is an actual line bundle on `X`. The definitions
`leftModuleIso` and `rightModuleIso` retain actual module-pullback
identifications with `L.obj` and `K.obj`. The theorem `compatible` is the
exact prescribed-overlap equation inherited from binary module gluing,
using the canonical square pullback comparison.

The namespace `OpenUnion` treats a pair that need not cover `X`. For a
morphism whose range is contained in an open `O`, `lift` factors it
through `O.toScheme`; `lift_ι` records the factorization, and an open
immersion remains an open immersion after this factorization. The maps
`left` and `right` factor `f` and `g` through the open union
`f.opensRange ⊔ g.opensRange`, and `cover` proves that they jointly cover
that union by unpacking point membership in its two images.

The scheme isomorphism `overlapIso` identifies the overlap of the two
factors over any containing open `O` with their overlap over the ambient
`X`. Both directions are pullback lifts using the unchanged projections;
the inverse direction uses that `O.ι` is a monomorphism. Its projection
formulas are recorded explicitly. The definition `overlap` pulls an
ambient module isomorphism back along this scheme isomorphism, then uses
canonical composition comparisons at the two ends. This gives a
specified isomorphism on the overlap over `O`, without asserting an
equality between the two scheme pullback objects.

Finally `OpenUnion.glue` uses this transported identification and the
two-chart covering construction to give an actual line bundle on the
open union. Its `leftModuleIso` and `rightModuleIso` identify the actual
pullbacks with the original bundles, and `OpenUnion.compatible` realizes
the transported identification on the overlap over the union. This
last equation is stated on that overlap; the module does not claim an
additional ambient-overlap comparison equation.

All schemes lie in arbitrary universe `u`. There are no integrality,
Noetherian, separatedness or finiteness assumptions. This unit supplies
binary gluing and geometric overlap transport. Local extension,
preservation of all prior atlas transitions and the maximal-atlas
coverage argument are further obligations of the general extension task.

The local rank-one and composite-pullback comparisons reuse the published
`IsLocallyFreeRankOne.exists_of_pullback` and `Langlands.Scheme.Modules.compIso`
through the existing general-cover gluing import. Their hypotheses, conclusions
and composite isomorphisms agree with the submitted helper copies.
