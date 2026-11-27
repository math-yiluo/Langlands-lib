# Étale descent for the normalized CM classes on connected admissible tests

The module `Langlands.Shimura.PEL.HarrisTaylorCMConnectedEtaleSheafStatement`
defines one proposition, `CMConnectedEtaleSheafStatement`. It is the
restriction of `CMSmallLevelEtaleSheafStatement`
(`Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientPremiseStatements`) to
connected admissible tests. The module states it and does not prove it.

## Data

The proposition takes the same parameters as `CMSmallLevelEtaleSheafStatement`:
the universe-zero number fields `E`, `F`, `L`, the algebra `A`, the central
simple unitary datum `D`, the embedding `τ₀`, the Harris signature charts `C`
on `harrisCMSection E (algebraMap L F) τ₀`, and the named prerequisites
`preservation`, `composition`, `unitCoherence`, `associativity`, `comparison`,
`symmetry`, `stability`, `square`, `universality`, `dualityNaturality`,
`polarizationStability`, `compatibility`, `h` and `htor`. They are parameters
of the definition, not assertions.

Write `Bases` for `AdmissibleCMBaseCategory D C …`
(`Langlands.Shimura.PEL.HarrisTaylorCMPolarizedUnpointedPresheaf`): the full
subcategory of schemes over `Spec F` satisfying `AdmissibleCMBase`, with all
morphisms over `Spec F`. Every object of `Bases` has a connected, locally
noetherian, quasi-separated underlying scheme. Write `Q` for
`unpointedClassTowerPresheaf D C …`, the presheaf
`Basesᵒᵖ ⥤ (HarrisLevel D ⥤ Type 1)` of unpointed normalized CM classes on
connected tests. Its value at a test `X` and a Harris level `V` is
`(unpointedClassTower … X).obj V`, the compatible families, over all
geometric points of `X`, of normalized joint classes of polarized abelian
schemes with `A`-action, normalized CM Lie condition and monodromy-invariant
adelic level orbit, up to rational isogeny. Its restriction along a test
morphism `f` is `unpointedClassTowerPullback … f`.

## The proposition

`CMConnectedEtaleSheafStatement` says: for every small level
`U : SmallCMLevel D`, every connected admissible test `S : Bases`, every index
type `K : Type`, every family `W : K → Bases` and every family of test
morphisms `g k : W k ⟶ S` such that

- each underlying scheme morphism `(g k).hom.left` is étale, and
- every point of `S` is the image of a point of some `W k`,

the presheaf `Q.flip.obj U.obj : Basesᵒᵖ ⥤ Type 1` of classes at level
`U.obj` satisfies `Presieve.IsSheafFor (Q.flip.obj U.obj)
(Presieve.ofArrows W g)`. That is, every family of classes on the `W k` that
is compatible in Mathlib's sense is the restriction of exactly one class on
`S`. Compatibility is tested in `Bases`: for every connected admissible test
`Z` with morphisms `a : Z ⟶ W k` and `b : Z ⟶ W l` satisfying
`a ≫ g k = b ≫ g l`, the two pullbacks to `Z` agree.

## Relation to the disconnected statement and provenance

The disconnected class presheaf `(smallLevelClassPresheafTower …).obj U` of
`CMSmallLevelEtaleSheafStatement` is, by its definition
(`disconnectedClassTowerPresheaf`), the product over the actual connected
components of a test of the presheaf `Q` above. The module
`Langlands.Shimura.PEL.HarrisTaylorCMEtaleSheafComponentReduction` proves
that `CMConnectedEtaleSheafStatement` implies `CMSmallLevelEtaleSheafStatement`
(`cmSmallLevelEtaleSheafStatement_of_connected`).

The proposition is internal to the Library. Its informal source is the same
as that of `CMSmallLevelEtaleSheafStatement`: Harris–Taylor, *The Geometry
and Cohomology of Some Simple Shimura Varieties* (2001), III.1, p.91
(`harris-taylor-2001-geometry-cohomology-simple-shimura`), and Kottwitz,
*Points on some Shimura varieties over finite fields* (1992), §5, p.391
(`kottwitz-1992-points-shimura-finite-fields`), assert that for small levels
their moduli functors are representable, hence étale sheaves. Those
assertions are made under narrower hypotheses; the proposition here concerns
the Library presheaf for general central simple unitary data, restricted to
connected tests.
