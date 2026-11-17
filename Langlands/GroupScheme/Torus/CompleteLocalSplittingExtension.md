# Finite étale local extensions for splitting special fibres

This derived prerequisite constructs actual finite étale local extensions used
in the complete-local deformation argument. The base ring `A` may be any
commutative local ring. The construction does not require completeness,
noetherianity, or smoothness. Completeness of the resulting extension is proved
separately when `A` is complete and noetherian.

`ResidueExtensionData A K` consists of a local finite étale `A`-algebra `L`, a
local structural map, and a surjective `A`-algebra homomorphism `L → K`, where
`K` is a field with a specified `A`-algebra structure. Its derived interfaces
prove that `L` is finite free and faithfully flat over `A`, and that
`Spec L → Spec A` is finite, étale, and surjective. The surjection identifies
the residue field of `L` with `K` by `residueFieldEquiv`, with an explicit
compatibility formula on residue classes.

`residueExtension A K` constructs this data when `K` is a finite separable
extension of the residue field of `A`, and the specified `A`-algebra structure
is compatible with that extension. The extension is finite and formally
unramified over `A`, and its structural map is local. A field is Henselian, so
the published `UnramifiedFunctor.CompleteLocal.exists_etaleCover`, applied
with target `K`, provides a finite étale local algebra surjecting onto `K`.
The composite structural map to `K` proves locality of `A → L`.

For any such data, formal unramifiedness gives
`maximalIdeal A · L = maximalIdeal L`. If `A` is noetherian and complete for
its maximal ideal, the published finite-module completeness theorem
`IsAdicComplete.of_finite_of_isNoetherianRing` makes `L` complete as an
`A`-module. The change-of-ideal comparison
`IsAdicComplete.map_algebraMap_iff` and the maximal-ideal identity then prove
that `L` is complete for its own maximal ideal.

`isFieldMultiplicativeType` passes from the relative fppf-local predicate to
the field-extension predicate. Choose a point of a splitting-cover member
above the unique point of the field spectrum and pull the supplied model
back to its residue field. The published `baseChangeCompIso` and
`Diagonalizable.relativeModelIso` compare this with the affine diagonalizable
model over that field. No separability of this intermediate field is asserted.

`SpecialFibreSplittingData A G` packages a finite Galois extension `K` of the
residue field of `A`, a finitely generated abelian character group `N`, an
actual diagonalizable presentation of `G_K`, and `ResidueExtensionData A K`.
The constructor `specialFibreSplitting A G hG` requires only that the special
fibre of `G` satisfies the relative multiplicative-type predicate. It applies
the preceding field comparison and the published theorem
`multiplicativeTypeFiniteGaloisSplitting`, then lifts the resulting field
extension by `residueExtension`.

`coverFibreIso` compares successive base change to `L` and then its quotient
`K` with direct base change from `A`. Finally,
`specialFibre_isDiagonalizable` uses the explicit residue-field isomorphism
to prove diagonalizability of the actual special fibre of `G_L`, along
`Spec.algebraMap L (ResidueField L)`.

These are internal constructions derived from published field splitting,
finite unramified local covering, and completeness results. They implement
the field-splitting reduction used in Conrad (2014), Theorem B.3.2(2),
pp.288–289. They do not lift a diagonalizable presentation from a special
fibre to the whole group over `L`, prove adic effectivity, or prove the
complete-local deformation statement.
