# Maximal tori on residue fibres and supplied field-valued fibres

This internal unit defines `IsFibrewiseMaximalTorus i` for a map
`i : T.toGrp ⟶ G`, where `T` is a commutative group scheme over an arbitrary
scheme `S`. It is the Prop-valued assertion that the actual pullback of `i`
along `S.fromSpecResidueField s` is a maximal torus for every point `s : S`.
The source in each predicate is the actual commutative base change of `T`.

For a smooth affine ambient group, maximality on these residue fibres implies
maximality on every supplied field-valued fibre `b : Spec k ⟶ S`, with
`k : Type u` in the same universe as `S`. The lemma
`isMaximalTorus_fieldPoint_of_residueFibre` needs maximality only at
`s = b (IsLocalRing.closedPoint k)`. The proof equips `k` with the algebra
structure induced by `fieldPointResidueMap b`, applies
`maximalTorusBaseChange` to the residue-fibre group and torus, and uses
`isMaximalTorus_of_baseChange_comp` to compare the successive pullbacks with
the pullback along the composite. Rewriting
`fieldPointResidueMap_factorization` identifies that composite with the
original supplied map `b`. The result retains the original pullback of `i`
and its actual source.

`IsFibrewiseMaximalTorus.fieldPoint` applies this construction to a fibrewise
maximal torus. The equivalence
`isFibrewiseMaximalTorus_iff_forall_fieldPoint` identifies the residue-fibre
condition with maximality on every supplied field-valued point. Its reverse
direction specializes to the residue field and its canonical map.
These general results need no local or reductive hypothesis on the base.

Over a commutative local ring `R`,
`IsReductive.isMaximalTorus_fieldPoint_of_closedFibre` applies to an arbitrary
closed split torus in a reductive group whose actual closed residue fibre is
maximal. The existing
`IsReductive.isMaximalTorus_residueFibre_of_closedFibre` first gives the needed
maximality at the image of `b`. The preceding field-point lemma then applies.
Smoothness and affineness are obtained from the supplied reductivity proof;
they are not additional assumptions.

The namespace `splitTorus` supplies two coordinate-torus specializations. For
a finite coordinate type `I`,
`isMaximalTorus_baseChangeHom_of_fibrewise` transfers the result along the
canonical `baseChangeIso` to the standard coordinate torus over a supplied
field algebra `k`. Its map is exactly `baseChangeHom (K := k) G I i`, using
the original `R`-algebra structure. The local reductive specialization
`isMaximalTorus_baseChangeHom_of_closedFibre` obtains the residue-fibre
condition from closed-fibre maximality. This last result assumes a closed
subgroup and a decidable equality on the finite coordinate type, as required
by the existing propagation theorem. Its ambient smoothness and affineness
also follow from reductivity.

The provenance is internal: the new transport is a direct composition of the
Library's canonical residue-field factorization, maximal-torus field-extension
theorem, and composite-pullback and source-isomorphism transports. The local
corollaries use the existing local closed-fibre propagation theorem. No new
external structural assertion is introduced. This unit transports maximality
of a supplied torus; it does not construct a torus, an integral representation,
root data, or an integral group-scheme isomorphism, and does not prove
`StrictHenselianGenericIsoStatement`.
