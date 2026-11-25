# The centralizer of a large identity jet is the centre

`Langlands.GroupScheme.JetCentralizerStabilizationStatement.{u}` is a
`Prop`-valued definition, stated over an affine base.

## Hypotheses and conclusion

Let `R : CommRingCat.{u}` and let `G : GroupScheme (Spec R)` have a smooth,
separated and quasi-compact structure morphism. For every point `s`, the
underlying space of the residue-field group
`RelativeIdentityComponent.residueFiber G s` must be connected.

The conclusion asserts that some natural number `n` works for every test
scheme `U : Over (Spec R)`. If a point `g : U ⟶ G.X` satisfies
`IdentityJet.CentralizesJet G n g`, then `g * h = h * g` for every
`h : U ⟶ G.X`. The predicate `CentralizesJet` says that `g` commutes with
every point of the order-`n` identity jet after every refinement of `U`.
So the centralizer of the jet is contained in the centre. The reverse
inclusion is immediate and is not part of the statement.

## Source correspondence

SGA 3, Exposé XI, Corollary 6.11 applies to `G` locally of finite type and
quasi-separated over `S`, and to a smooth subgroup `H` of finite presentation
with connected fibres. Part (b) says that if `G` is quasi-compact, there is
`n > 0` with `Centr_G(H) = Centr_G(H_n)`, where `H_n` is the `n`-th
infinitesimal neighbourhood of the unit section of `H`. Take `H = G`. A
smooth, separated, quasi-compact morphism is of finite presentation and
quasi-separated. The connected-fibre hypothesis is the residue-field
condition above. Then `Centr_G(G)` is the centre. The infinitesimal
neighbourhood `G_n` is the Library's `IdentityJet.scheme G n`, and
`Centr_G(G_n)` is the functor of points satisfying
`IdentityJet.CentralizesJet G n`.

The proof of 6.11(b) applies Corollary 6.10 over the base `G`. That
corollary asserts the stabilisation `Π_{X/S} Y/X = Π_{X_n/S} Y_n/X_n` for
`n` large when the base is quasi-compact. Here the base is affine and `G` is
quasi-compact over it.
[SGA 3, Exposé XI, Corollaries 6.10 and 6.11](https://wstein.org/sga/SGA3/Expo11.pdf#page=33).

SGA 3 assumes only that `G` is quasi-separated. The statement assumes that
`G` is separated, which is stronger. Then the unit section is a closed
immersion, and `IdentityJet.scheme G n` is the infinitesimal neighbourhood
of the unit section. It is used with a separated group in the proof of
`Langlands.GroupScheme.LocalCentralKernelRepresentationStatement`.

## Registered sources

- A. Grothendieck, SGA 3, Exposé XI, Gille–Polo recomposition (December
  2008), Corollaries 6.10 and 6.11(b) with their proofs, printed
  pp. 117–118 (original pp. 177–179), one-based PDF pp. 33–34.
  `Expo11.pdf` in `sga3-exposes-xi-xii-xiv-gille-polo-2008`.
