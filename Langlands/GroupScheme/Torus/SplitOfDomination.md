# Tori dominated by split tori

All groups in this module are over an arbitrary field `k : Type u`.
The construction `IsSplitTorus.dominantPresentation` takes a split
commutative group scheme `D`, an affine group scheme `H`, and a homomorphism
`φ : D.toGrp ⟶ H` that is schematically dominant on the underlying schemes.
It retains the published dominant split-image factorization and adds an
actual group-scheme isomorphism from its split image to `H`. The equation
`inclusionIso_hom` identifies that isomorphism's forward map with the
factorization's closed inclusion. The inherited `factor_comp` equation
still identifies the composite with the supplied homomorphism.

The supporting theorem `DominantFactorization.isIso_inclusion` uses the
factorization equation. The ideal sheaf kernel of the closed inclusion
is contained in the ideal sheaf kernel of its composite with the factor
map. Schematic dominance makes the latter zero. A closed immersion with
zero ideal sheaf kernel is an isomorphism of schemes. The forgetful
functor to schemes and the group-object isomorphism constructor lift this
to an actual group-scheme isomorphism. This argument does not assume
that `H` is reduced.

`IsSplitTorus.of_schematicallyDominant_hom` therefore proves splitness of
every affine group scheme that is a schematically dominant homomorphic
image of a split torus. Its source may be supplied as a group scheme;
a splitting isomorphism reduces to the commutative canonical model.

`IsTorus.isSplitTorus_of_pointed_schematicallyDominant_morphism` applies
this result to an underlying scheme morphism `p : D.X ⟶ H.X` between a
split torus `D` and an arbitrary torus `H` satisfying the identity equation
`η[D.X] ≫ p = η[H.X]`. The pointed-morphism constructor supplies the
homomorphism with exactly that underlying morphism, and torus affineness
supplies the affine target hypothesis.

`IsTorus.isSplitTorus_of_pointed_dominant_morphism` needs only topological
dominance of `p.left`: the torus target is smooth over the field and hence
reduced, so dominance implies schematic dominance. Finally,
`HasPointedSplitTorusDomination.isSplitTorus` applies the result directly
to the published pointed split-torus domination predicate and a supplied
torus target. The predicate's identity-point equation is converted to the
monoidal unit equation used by the pointed-morphism constructor.

This is an internal deduction from the split-image factorization,
pointed-morphism rigidity, torus geometry, and ideal sheaf kernel APIs.
There are no characteristic, perfectness, infinitude, or ground-field
splitness restrictions on the target before the conclusion. It supplies
the torus case needed in the host solvable splitness argument. It proves
neither general solvable splitness nor splitness of a unipotent radical,
and does not prove full rational maximal-torus conjugacy.
