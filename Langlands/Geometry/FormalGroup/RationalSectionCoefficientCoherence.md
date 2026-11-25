# Coherence for successive coefficient changes of rational sections

This module proves the identity and composition coherence of the actual
coefficient pullback of rational Hom sheaf sections. It uses actual maps and
the existing canonical comparisons of coefficient-extended formal modules.

The coefficient ring `O` is commutative. The commutative `O`-algebras `R`, `S`
and `T` and the `O`-algebra field `F` occupy one universe; `O` may occupy
another. Coordinate types are finite and may differ. There are actual
`O`-algebra maps `φ : R →ₐ[O] S` and `ψ : S →ₐ[O] T`.

The inverse-image opens for the identity coefficient map and for successive
coefficient maps agree with the original open and with the inverse image
under the composite map, respectively. `coefficientSectionMap_id` and
`coefficientSectionMap_comp` identify the actual structure-section maps with
their identity and composite ring maps.

`Hom.transportIsoLinear` is the actual `O`-linear conjugation by a pair of
integral isomorphisms, with its exact coordinate-series formula.
`RationalHom.transportIsoLinear` tensors this map with `F`. Its pure tensor
formula and its agreement with composition by the two rationalized integral
maps are proved by tensor induction. `transportIso_ofRational` identifies
actual sheaf-section transport of a representative with this tensor transport
through the coefficient extensions of the same two integral isomorphisms.

`baseChange_identity_transport` states that pullback along the identity
coefficient map, followed by transport through `mapIdIso` on source and target,
is the original section.
`baseChange_composite_transport` states that successive pullbacks along `φ`
and `ψ`, followed by transport through `mapCompIso` on source and target,
give the pullback along `ψ.comp φ`, restricted along the canonical equality
between the successive inverse-image open and the composite inverse-image
open. This uses the actual sheaf restriction map along `eqToHom` of that
proved equality, so both sides are sections on the same displayed open.

For each equality, the proof first establishes the formula on rational tensors.
Tensor induction reduces it to equality of actual integral coordinate series.
The canonical comparison maps have identity coordinate series. The formulas
for the actual structure-section ring maps therefore give the required
identity or composition of coefficients. On arbitrary sheaf sections,
the covering image sieve of the genuine sheafification unit supplies local
representatives. Restriction compatibility and separatedness of the actual
target sheaf give the whole-open equality. In the composite case this is the
successive actual pushforward through `Spec T → Spec S → Spec R`;
naturality of the canonical equality of opens follows from the thinness of
the open-set category. The representative calculation is isolated before
the covering-sieve argument.

No global representative, fraction-field, nilpotence or isogeny hypothesis
is imposed. This module does not construct the moduli functor or a local
quasi-isogeny inverse.
