# Propagating maximality from the closed fibre

This module proves that, over any commutative local ring `R`, an actual closed
split commutative torus `i : T.toGrp ⟶ G` in a reductive group scheme `G` over
`Spec R` is maximal on every actual residue-field fibre whenever its closed-fibre
inclusion is maximal. Henselianity and separable closedness are not needed for
this step. The module does not construct the torus; it only propagates
maximality of a supplied one.

## Main statement

`LocalClosedFibreMaximalPropagationStatement.{u}` is the Prop-valued packaging:
for every `R : Type u` with `[CommRing R] [IsLocalRing R]`, every `G` with
`IsReductive G`, every `T : CommGroupScheme (Spec R)` and `i : T.toGrp ⟶ G` with
`IsSplitTorus T.toGrp` and `IsClosedSubgroup i`, maximality of
`(baseChange (fromSpecResidueField (closedPoint R))).map i` (source the
commutative base change of `T`) implies maximality of
`(baseChange (fromSpecResidueField s)).map i` for every point `s`. The fibres
are the actual pullbacks along `Scheme.fromSpecResidueField`, exactly as in
`StrictHenselianSplitMaximalTorusStatement`. The theorem
`localClosedFibreMaximalPropagation` proves it, as a direct application of
`IsReductive.isMaximalTorus_residueFibre_of_closedFibre`.

## Proof structure

The standard-torus lemmas live in namespace `splitTorus`, over a commutative ring
`r`, for the standard split torus `i : splitTorus (Spec r) I ⟶ G` with `G` smooth
and affine over `Spec r`:

- `isMaximalTorus_geometricFiberHom_of_residueFibre`: maximality on the residue
  fibre at `s` transports through `baseChangeIso` to the base-changed standard
  torus map, then extends to the chosen algebraic closure of the residue field by
  `isMaximalTorus_fieldPoint_extension`. This uses the published self-centralizer
  theorem `maximalTorusCentralizer`, and yields maximality of
  `geometricFiberHom I G i s`.
- `isMaximalTorus_residueFibre_of_geometricFiberHom`: the reverse direction, for
  a closed subgroup. It transports through `baseChangeIso`, identifies the
  geometric pullback as a composite pullback by `isMaximalTorus_baseChange_comp`,
  and reflects along the algebraic-closure extension by
  `IsMaximalTorus.of_baseChange`.
- `geometricPoint_closedPoint`: the chosen geometric point over `s` sends the
  closed point of the algebraic closure to `s`.
- `mem_geometricSelfCentralizingTorusLocus_of_geometricFiberHom`: for reductive
  `G`, geometric maximality at `s` places `s` in
  `geometricSelfCentralizingTorusLocus I G i`. The identity-component
  reductivity needed by `mem_geometricSelfCentralizingTorusLocus_of_maximal_fieldPoint`
  comes from connected reductivity of the algebraically closed geometric fibre.
- `isMaximalTorus_geometricFiberHom_of_mem`: conversely, on that locus
  `isMaximalTorus_geometricIdentityComponentHom_of_mem` gives maximality in the
  geometric identity component. Reductivity makes the geometric fibre connected,
  so `IdentityComponent.connectedIso` identifies the identity component with the
  whole fibre, and `geometricIdentityComponentHom_comp` recovers
  `geometricFiberHom I G i s`.
- `mem_geometricSelfCentralizingTorusLocus_of_closedPoint`: over a local ring,
  every point specializes to the closed point, and the locus is open by
  `isOpen_geometricSelfCentralizingTorusLocus` (a closed subgroup is required).
  So a locus containing the closed point contains every point.
- `isMaximalTorus_residueFibre_of_closedFibre`: these steps combine to go from
  the closed residue fibre to the geometric closed fibre, into the locus, to
  every point, and back to every actual residue fibre.

The general wrapper works outside the namespace:

- `isMaximalTorus_baseChange_inv_comp_iff`: over a field-valued point
  `b : Spec k ⟶ S`, precomposing an inclusion with the inverse of a source
  isomorphism `e : T.toGrp ≅ T'.toGrp` does not change maximality of the actual
  pullback. This follows from `Functor.map_comp` and `IsMaximalTorus.iso_comp_iff`
  along `(baseChange b).mapIso e.symm`.
- `IsReductive.isMaximalTorus_residueFibre_of_closedFibre`: a splitting
  `e : T.toGrp ≅ splitTorus (Spec R) I` of the supplied commutative torus turns
  `i` into the standard closed subgroup `e.inv ≫ i` (via
  `IsClosedSubgroup.iso_comp`). The closed-fibre hypothesis transfers to it by
  the previous lemma, the standard-torus theorem applies, and the result
  transfers back. Each fibre keeps the pullback of the original `i`, with source
  the commutative base change of the original `T`.

## Provenance

This is internal infrastructure, derived from Library theorems used by their
Lean names: the self-centralizer theorem, field-extension ascent and descent of
maximality, openness of the relative geometric self-centralizing torus locus,
and the base-change transport lemmas. It is not a transcription of a literature
proof, and no new external assertion is introduced.
