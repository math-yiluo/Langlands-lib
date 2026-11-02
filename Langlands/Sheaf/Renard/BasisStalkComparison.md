# Renard II.2.1: stalks before and after restriction to a chosen basis

The governing source is Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The final paragraph of II.2.1, printed p.37 / PDF p.43, begins "Terminons
cette section". It restricts a sheaf `G` of base `T` to the chosen basis `T0`
and forms the germ extension `(G_T0)+`. It then states "Il est clair que ce
faisceau est égal à G+". That claim compares the stalks of `G_T0`, a filtered
colimit over basis neighborhoods, with the stalks of `G`, a filtered colimit
over all open neighborhoods. This module makes that stalk comparison explicit
on the actual colimits. The stalk is defined on printed p.34 / PDF p.40 as the
filtered colimit over the basis neighborhoods of a point. That page also
describes equality of germs through a common smaller neighborhood. The
supplementary corrections `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3, were read; none of them changes this comparison.

Throughout, `X : Type u` has its supplied topology, `B : OpenBasis X` is
arbitrary and `F : RawPresheaf.{u,v} (allOpenBasis X)` is an arbitrary
all-open raw presheaf. Its restriction is the published
`(rawBasisRestriction B).obj F`, precomposition with `basisToAllOpen B`.

## Finality of chosen basis neighborhoods

`neighborhoodToAllOpen B x` sends a chosen basis neighborhood `V` of `x` to
the same actual open, regarded as an object `allOpen V.obj` of the all-open
basis. `neighborhoodToAllOpen_comp_inclusion` records that it lies over the
basis inclusion `basisToAllOpen B`.
`stalkDiagram_rawBasisRestriction` states that the published stalk diagram
of the restriction is, by definition, this functor followed by the
published stalk diagram of `F`. Neither stalk diagram is changed.

`exists_neighborhoodToAllOpen_hom` is basis refinement: each actual open
neighborhood `W` of `x` contains a chosen basis neighborhood, by
`OpenBasis.exists_subset`. The instance `neighborhoodToAllOpen_final`
proves finality from Mathlib's `Functor.final_of_exists_of_isFiltered`.
That criterion requires the source category of chosen basis neighborhoods
to be filtered. This is the published `IsFiltered (BasisNeighborhood B x)`
instance of `Langlands.Sheaf.Renard.BasisStalk`, which also comes from
basis refinement. The criterion's first condition is the refinement above.
Its second condition, agreement of parallel morphisms into an image object,
holds with the identity because the all-open neighborhood category is thin
(the published `Subsingleton` instance on its morphisms). Finality is proved
here and is not assumed as a hypothesis.

## The comparison isomorphism

`rawStalkRestrictionIso B F x` is Mathlib's `Functor.Final.colimitIso` for
this final functor. It is an isomorphism between the two published colimits
`rawStalk ((rawBasisRestriction B).obj F) x` and `rawStalk F x`. Its forward
map is the colimit comparison `colimit.pre` (`rawStalkRestrictionIso_hom`).
`rawStalkRestrictionEquiv B F x` is the same isomorphism as an additive
equivalence. It is the map `c_(B,F,x)` of the task. Its point formulas
`rawStalkRestrictionEquiv_apply` and `_symm_apply` are the hom and inverse
of the categorical isomorphism.

`rawStalkRestrictionEquiv_germ` evaluates the forward map on germs. For an
original section `t : Sections F (allOpen V.obj)` on a basis open `V`
containing `x`, the restricted germ `rawGerm ((rawBasisRestriction B).obj F)
V x hx t` goes to the original germ `rawGerm F (allOpen V.obj) x hx t`. This
is the colimit-insertion formula `Functor.Final.ι_colimitIso_hom`.
`rawStalkRestrictionEquiv_symm_germ` is the inverse equation on the same
germs. `rawStalkRestrictionEquiv_symm_germ_of_le` handles an original germ
on an arbitrary actual open `W`. For any chosen basis open `V ≤ W`
containing `x`, the inverse sends that germ to the restricted germ of the
original restriction of the section to `V`. Its proof is the published
`rawGerm_restriction` law followed by the inverse germ equation.

## Naturality and functor packaging

`rawStalkRestrictionEquiv_naturality` proves, for every original natural
transformation `φ : F ⟶ G`,
`c_(B,G,x) ∘ rawStalkMap ((rawBasisRestriction B).map φ) x =
rawStalkMap φ x ∘ c_(B,F,x)`. The proof writes an arbitrary restricted stalk
element as a germ, using the published representative theorem
`rawStalk_representative`. It then applies the germ formula above and
`rawStalkMap_germ` on both sides.
`rawStalkRestrictionEquiv_symm_naturality` is the inverse equation, and
`rawStalkRestrictionIso_hom_naturality` is the commutative square of actual
stalk maps.

`rawStalkRestrictionNatIso B x` packages the components as a natural
isomorphism
`rawBasisRestriction B ⋙ rawStalkFunctor B x ≅ rawStalkFunctor (allOpenBasis X) x`.
Its component at `F` is `rawStalkRestrictionIso B F x`
(`rawStalkRestrictionNatIso_app`). The normalized specialization
`stalkRestrictionNatIso B x` is
`basisRestriction B ⋙ stalkFunctor B x ≅ stalkFunctor (allOpenBasis X) x`.
It is obtained by whiskering with the existing `presheafInclusion`, and its
components are the same isomorphisms (`stalkRestrictionNatIso_app`). No new
presheaf category or stalk carrier is introduced.

## Scope and generality

The space universe `u` and the original section universe `v` are
independent; both stalks are the published colimits in `Type (max u v)`, and
no lowering to `v` is asserted. The input is an arbitrary raw presheaf: no
normalization, sheaf or separation hypothesis is used. Arbitrary supplied
topologies and arbitrary chosen bases are allowed; no intersection closure
is required. Empty spaces and empty opens are allowed. No compactness, total
disconnectedness, Hausdorff, countability, nonemptiness or cardinality
hypothesis is used. The raw-input, arbitrary-topology and categorical
formulation is an internal generalization. It supports the source's
basis-independence passage, which concerns sheaves.

This comparison changes the input basis and the colimit diagram. It is
different from the published `rawAllOpenGermRestrictionIso` of
`Langlands.Sheaf.Renard.SheafBasisRestriction`. That isomorphism has
identity components and evaluates the same original stalk family on
different target bases. The germ-section transport and the natural
isomorphism of the all-open germ-sheaf functors built from this comparison
are in `Langlands.Sheaf.Renard.GermSectionBasisComparison`. This module does
not prove the equivalence of sheaf categories at the original value universe,
any universe lowering, compact-section comparisons or scalar/module
structures; those remain separate obligations.
