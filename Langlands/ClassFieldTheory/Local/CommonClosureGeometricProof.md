# Normalized common-closure reciprocity families are geometric: proof

`Langlands.LocalClassField.commonClosureGeometricProof` proves
`Langlands.LocalClassField.CommonClosureGeometricStatement.{u, v}` with no further hypotheses.
Fix a p-adic field `F` and a reciprocity family `eC` with
`LocalFactor.CommonClosure.NormalizedReciprocity F eC`. Its norm relation is `he.1.1` and its
geometric normalization is `he.2`.

## Clause 1: candidates of `F`

This clause is the existing Library theorem
`Correspondence.isGeometricReciprocity_of_isBaseReciprocity F e eC h he`.
`Correspondence.IsGeometricReciprocity F e` abbreviates
`GeometricWeilReciprocityRelation F F.canonicalTopologicalData e`.

## Clause 2: a finite extension `E`, given by `g : F →ₐ[ℚ_p] E`

Write `e' := extensionReciprocityCandidate F E g eC`. The Library theorem
`Correspondence.isGeometricReciprocity_of_localCandidate E e'` reduces the clause to
`LocalReciprocityCandidateRelation` for `e'`. It derives the Frobenius condition from the
order relation. The order relation is the Library theorem
`extensionReciprocityCandidate_geometricOrder F E g eC he.2`. The remaining part is
`ProfiniteNormResidueRelation` for the inverse candidate. The theorem
`CommonClosureGeometric.profiniteNormResidue_extensionReciprocityCandidate` proves it from
the norm relation `he.1.1`. Its three parts come from the following results.

- **Density.** `FiniteArtinReconstruction.denseRange_of_finite_surjective`, applied to the
  finite surjectivity `Correspondence.finiteRestriction_surjective E e'`.
- **Compatibility.** `ProfiniteReciprocityReconstruction.finiteFamilyOfHom_compatible`.
- **Finite norm-residue isomorphisms.** For each finite abelian extension `L` of `E`, the
  finite restriction is surjective by `Correspondence.finiteRestriction_surjective`. Its
  kernel is `normSubgroup E L` by
  `CommonClosureGeometric.finiteNormKernel_extensionReciprocityCandidate`, proved as follows.

### The kernel at a finite abelian extension `L` of `E`

Let `τ := extensionClosureEquiv F E g : F̄ ≃+* Ē` and let `E'` be the image of `E` in `F̄`
(`extensionFiniteIntermediate F E g`).

1. `imageField F E g L` is the intermediate field `M' := τ⁻¹(L)` of `F̄` over `F`. It
   contains `E'` (`extensionIntermediateField_le_imageField`). The map `x ↦ τ⁻¹ x` is a field
   isomorphism `imageFieldEquiv : L ≃+* M'`. Together with the ring isomorphism
   `baseEquiv : E ≃+* E'` from `extensionIntermediatePadicEquiv`, it forms a commuting square
   with the algebra maps (`imageFieldEquiv_compatible`). Hence `M'` is finite over `E'`, and
   so over `F`. This gives the finite intermediate extension `imageExtension F E g L`.
2. `restriction_eq_one_iff`: for `σ ∈ G_E`, `L.restriction σ = 1` iff
   `extensionGaloisMap F E g σ` fixes `M'`. The proof uses `restrictNormalHom_ker` and the
   defining relation `extensionClosureLift_galoisMap`.
3. `projection_mem_range_iff`: for a Weil element `w` of `E`, the abelianized image of
   `extensionImageWeilEquiv F E g w` lies in the range of
   `E'.weilAbelianInclusion M'` iff `L.restriction` of the Galois projection of `w` is
   trivial. The forward direction applies `abelianizationLift` of the continuous
   homomorphism `L.restriction ∘ localProjection E ∘ (extensionImageWeilEquiv F E g)⁻¹`. This
   homomorphism kills the Weil subgroup of `M'` by step 2. For the converse, step 2 places
   the image of `w` in the Weil subgroup of `M'`.
4. `unitsEquiv_symm_mem_normSubgroup_iff`: for `x ∈ E'ˣ`,
   `(extensionIntermediateUnitsEquiv F E g)⁻¹ x ∈ normSubgroup E L` iff `x` is a norm from
   `M'ˣ`. This is `FiniteArtinTransport.mem_normSubgroup_map_iff` for the square of step 1.
5. Every element of the source of the inverse candidate is `e'(mk w)` for a Weil element `w`.
   `Correspondence.finiteRestriction_reciprocityHom` identifies its finite restriction with
   `L.restriction` of the Galois projection of `w`. By definition of `e'`, its value is
   `(extensionIntermediateUnitsEquiv F E g)⁻¹ (eC E' (mk (extensionImageWeilEquiv F E g w)))`.
   `ReciprocitySystemUniqueness.symm_mem_range_iff he.1.1` at `E' ≤ M'`, applied to
   `eC E' a`, says that `a` lies in the range of `E'.weilAbelianInclusion M'` iff
   `eC E' a` is a norm from `M'ˣ`. Steps 3 and 4 then give the kernel equality.

The final theorem assembles the two clauses. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
