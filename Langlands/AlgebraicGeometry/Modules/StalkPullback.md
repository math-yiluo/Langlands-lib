# Stalks of ordinary module pullback

For arbitrary schemes `X Y : Scheme.{u}`, a morphism `f : X ⟶ Y`, and a
point `x : X`, `StalkPullback.pullbackStalkIso f x` is a natural
isomorphism from ordinary module pullback followed by the actual module
stalk at `x` to the actual module stalk at `f x` followed by extension of
scalars along `(f.stalkMap x).hom`. Both functors take actual module
sheaves and actual module morphisms; no quasi-coherence hypothesis is
needed.

For an actual module sheaf `M` on `Y`,
`StalkPullback.pullbackStalkTensorEquiv f x M` consequently gives the
`𝒪_{X,x}`-linear equivalence

`(f* M)_x ≃ 𝒪_{X,x} ⊗[𝒪_{Y,f(x)}] M_{f(x)}`.

The algebra structure in this expression is explicitly
`(f.stalkMap x).hom.toAlgebra`, and the source uses the canonical local-ring
action on the actual abelian-group stalk. The comparison with the ordinary
algebra tensor product uses the published `extendScalarsAlgebraEquiv`.

The construction first identifies the right adjoints. Pushforward of the
skyscraper module at `x` is the skyscraper module at `f x` with local-ring
scalars restricted through `f.stalkMap x`. The comparison in each
direction is the identity on functions witnessing membership in an open;
its linearity is precisely compatibility of the scheme morphism's germ
and stalk maps. This yields `skyscraperPushforwardIso`, natural in the
local-ring module. Compose the ordinary pullback-pushforward adjunction
with the module stalk-skyscraper adjunction, transport its right adjoint
through this comparison, and compare with the composite of the target
stalk-skyscraper and extension-restriction adjunctions. Uniqueness of left
adjoints gives `pullbackStalkIso`.

The provenance is internal. This is a derived comparison of the actual
Mathlib pullback, stalk and scalar-extension constructions, using the
explicit module skyscraper adjunction from `StalkAdjunction`; it makes no
direct claim from the original coherent-family source. It supplies
infrastructure for relative-flatness preservation and point-fibre
comparisons. Those consequences and the coherent-family groupoid are
separate obligations. The construction retains arbitrary schemes and the
universe `u`, with no finiteness, noetherianity or quasi-compactness
assumption.
