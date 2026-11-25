# Extending a rational algebra action on a good model over a DVR

Let `V` be a discrete valuation ring with fraction field `K`
and let `j : Spec K ⟶ Spec V` be the fraction-field morphism.
The declarations are in `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

`dvrGenericHom_bijective` shows that the existing base-change map on
homomorphisms between two abelian schemes over `Spec V` is bijective.
The source is flat and the target is separated, which gives injectivity.
Surjectivity comes from the published Néron mapping property for the
target abelian scheme. The bundled group-scheme maps and abelian-scheme
maps have the same underlying homomorphisms.

`dvrGenericRationalHom_bijective` extends this bijectivity to the
actual rationalized Hom groups. Base change is additive on integral
homomorphisms, giving an integral linear equivalence. Tensoring with
`ℚ` gives a rational linear equivalence. Checking the images of pure
tensors identifies its forward map with `rationalBaseChangeHom`.
On endomorphisms, the Library's `rationalBaseChangeEnd` is already a
unital `ℚ`-algebra homomorphism, so this gives `dvrRationalEndEquiv`.

`extendDvrRationalAction` composes a given rational algebra action on the
generic fibre of the model with the inverse of `dvrRationalEndEquiv`.
The restriction and uniqueness lemmas use the inverse and injectivity
equations of that equivalence. This extends the action once an abelian
scheme model has been obtained.

## Provenance

Derived from the Library's `genericFibre_map_injective`,
`baseChange_map_surjective` and `rationalBaseChangeEnd`.
The comparison of rational Hom groups uses Mathlib's linear extension
of scalars.
