# The centralizer of a split torus from the centralizers of its cocharacters

Throughout, `S` is a scheme, `T` a commutative group scheme over `S` and `G` a group
scheme over `S`, all in universe `u`.

## A split torus is a sum of cocharacter images

`IsSplitTorus.exists_sum_comp_eq_id`: if `T` is a split torus (`IsSplitTorus T.toGrp`,
that is, `T ≅ 𝔾_m^I` for a finite type `I`), then there are a finite type `I`, characters
`π j : characterLattice T` and cocharacters `s j : cocharacterLattice T` with
`∑ j, π j ≫ s j = 𝟙 T`. The sum is taken in the additive group of endomorphisms of the
commutative group scheme `T`; on points it is the product of the endomorphisms.

The proof takes the coordinate projections `splitTorus.proj` and coordinate inclusions
`splitTorus.single` of the standard split torus. They satisfy
`∑ j, proj j ≫ single j = 𝟙` (the published `splitTorus.sum_proj_comp_single`). The proof
transports them along the splitting isomorphism `e : T ≅ 𝔾_m^I`.

## Centralizing every cocharacter centralizes the torus

`le_torusCentralizer_of_le_dynamicCentralizer`: let `T` be a split torus,
`i : T.toGrp ⟶ G` a homomorphism and `F` a subgroup functor of `G`. Suppose that for every
cocharacter `c : cocharacterLattice T`, `F` lies in the dynamic centralizer
`Dynamic.centralizer (CommGroupScheme.groupHom c ≫ i)`. Then `F ≤ torusCentralizer i`.
This holds on every test scheme. No field, smoothness, affineness or reductivity is
assumed.

The proof starts from a point `g` of `F` over `U`, a morphism `a : V ⟶ U` and a point `t`
of `T` over `V`. By the first lemma, `t` is the product over `j` of the points
`t ≫ (π j ≫ s j)` (via `comp_groupHom_sum`). It therefore suffices that `a ≫ g` commutes
with the image of each factor under `i` (`Finset.prod_induction`). The factor
`t ≫ π j ≫ s j` is the image of the `𝔾_m`-point `t ≫ π j` under the cocharacter `s j`.
By hypothesis `g` lies in `Dynamic.centralizer (groupHom (s j) ≫ i)`. The published
`torusCentralizer_gm_eq_dynamicCentralizer` identifies this with
`torusCentralizer (groupHom (s j) ≫ i)`, whose defining condition at `a` and `t ≫ π j` is
the required commutation.

## Provenance

The lemma gives the inclusion `⋂_λ Z_G(λ) ⊆ Z_G(T)`, where `λ` runs over the cocharacters
of a split torus `T`. Together with the published `torusCentralizer_le_dynamicCentralizer`
(the reverse inclusion, one cocharacter at a time), it says that `Z_G(T)` is the
intersection of the centralizers of the cocharacters of `T`. The sources use the comparison
of `Z_G(S)` with the centralizer of one suitable cocharacter of a split torus `S`:
Borel–Tits, *Groupes réductifs* (1965), 4.15(a), printed pp.90–91 (PDF pp.37–38), source
`borel-tits-1965-groupes-reductifs`, and Milne, *Algebraic Groups* (2017), proof of
Theorem 25.6(b), printed p.546 (PDF p.562), source `milne-2017-algebraic-groups`. There
Milne chooses a cocharacter `λ` of `S` with `C_G(S) = C_G(λ(𝔾_m))`, citing 13.51. The
present lemma is an elementary ingredient of that comparison, not a statement quoted from
either source: a split torus is the product of the images of its coordinate cocharacters.
The formulation with subgroup functors on all test schemes over an arbitrary base is
derived. The file does not prove the equality for a generic cocharacter; it is one step
toward `GenericCentralizerStatement`.
