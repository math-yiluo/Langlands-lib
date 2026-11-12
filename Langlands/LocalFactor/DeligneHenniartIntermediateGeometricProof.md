# Geometricity of the intermediate components: proof

`Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.intermediateGeometricProof` proves
`Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.IntermediateGeometricStatement.{uF}`
(module `Langlands.LocalFactor.DeligneHenniartIntermediateUnits`) with no further hypotheses.
Its type is exactly that proposition.

Fix a prime `p`, a p-adic field `F`, a common-closure family
`eC : LocalFactor.CommonClosure.ReciprocityFamily F` with
`he : LocalFactor.CommonClosure.NormalizedReciprocity F eC`, and a finite intermediate field
`E : LocalFactor.CommonClosure.Extension F`. Write `EP := E.asPadicField`, `Ē` for the
algebraic closure of `E` and `F̄` for that of `F`. The candidate is
`e := intermediateReciprocityCandidate F eC E`, that is
`(abelianizationCongr (intermediateWeilEquiv F E)).trans (eC E)`. The proof uses `he.1.1`, the
family's `NormRelation`, and `he.2`, its `NormalizationRelation`. It does not use the
conjugation, transfer, density or completion relations.

The Library theorem `Correspondence.isGeometricReciprocity_of_localCandidate EP e` reduces the
goal `GeometricWeilReciprocityRelation EP EP.canonicalTopologicalData e` to
`LocalReciprocityCandidateRelation` for `e`. That theorem derives the Frobenius clause from the
order relation (`GeometricResidue.finite_congruence_of_geometricOrder`). Two facts remain, the
geometric order relation and `ProfiniteNormResidueRelation`.

This is route 2 of the task context: a direct argument at `E` itself. It follows the proof of
clause 2 of `CommonClosureGeometricStatement` in the published
`Langlands/ClassFieldTheory/Local/CommonClosureGeometricProof.lean`. Two changes are made.
The closure isomorphism `extensionClosureEquiv` is replaced by
`intermediateClosureEquiv F E : Ē ≃ₐ[E] F̄`, the isomorphism extending the literal inclusion of
`E` in `F̄`. The Weil identification `extensionImageWeilEquiv` is replaced by
`intermediateWeilEquiv F E`. The relevant component is therefore `eC E` at `E` itself, not at a
conjugate field. No conjugation argument is needed.

## Geometric order (`IntermediateGeometric.geometricOrder`)

- `weilDegree_abelianizationCongr`: for `w` in the abelianized Weil group of `EP`, the
  base-field degree `E.weilDegree (localResidueDegree F)` of its image under
  `abelianizationCongr (intermediateWeilEquiv F E)` is the degree of `w` raised to the power
  `f := extensionResidueDegree F EP (intermediateEmbedding F E)`. The proof is induction on the
  quotient followed by the definitional `localDegree_intermediateWeilMap`.
- `normalizedAbs`: the normalized absolute value of `e w` is `q_E ^ (-deg w)`. The
  normalization `he.2` at `E` gives `q_F ^ (-(f · deg w))`. The Library theorem
  `extensionResidueCardinality F EP (intermediateEmbedding F E)` gives `q_E = q_F ^ f`. The
  canonical data of `EP` is `canonicalData F E` by definition.
- `geometricOrder`: `normalizedAbs_of_ne_zero` rewrites the absolute value as
  `q_E ^ (-ord (e w))`. Since `q_E > 1`, `zpow_right_injective₀` gives `ord (e w) = deg w`.
  This is `GeometricOrderRelation`.

## Norm-residue relation (`IntermediateGeometric.profiniteNormResidue`)

- **Density.** `FiniteArtinReconstruction.denseRange_of_finite_surjective`, applied to the
  finite surjectivity `Correspondence.finiteRestriction_surjective EP e`.
- **Compatibility.** `ProfiniteReciprocityReconstruction.finiteFamilyOfHom_compatible`.
- **Finite norm-residue isomorphisms.** For each finite abelian extension `L` of `EP`, the
  finite restriction is surjective by `Correspondence.finiteRestriction_surjective`. Its kernel
  is `normSubgroup EP.Carrier L.field` by `IntermediateGeometric.finiteNormKernel`, proved as
  follows. Write `ι := intermediateClosureEquiv F E`.

1. `imageField F E L` is the intermediate field `M := ι(L)` of `F̄` over `F`. It is defined as
   the preimage of `L` under `ι⁻¹`. The lemma `closureEquiv_symm_coe` says that `ι⁻¹` sends an
   element `y` of `E` to its image in `Ē`. Hence `M` contains `F`, and it contains `E`
   (`field_le_imageField`). The map `x ↦ ι x` is a field isomorphism
   `imageFieldEquiv : L ≃+* M`. Together with the identity of `E` it forms a commuting square
   with the algebra maps (`imageFieldEquiv_compatible`, from `intermediateClosureEquiv_algebraMap`).
   Hence `M` is finite over `E`, and so over `F`. This gives the finite intermediate extension
   `imageExtension F E L`.
2. `restriction_eq_one_iff`: for `σ ∈ G_E`, `L.restriction σ = 1` iff
   `intermediateGaloisMap F E σ` fixes `M`. The proof uses `restrictNormalHom_ker` and the
   published relations `intermediateGaloisMap_apply` and `intermediateClosureEquiv_galoisMap`.
3. `projection_mem_range_iff`: for a Weil element `w` of `EP`, the abelianized image of
   `intermediateWeilEquiv F E w` lies in the range of `E.weilAbelianInclusion M` iff
   `L.restriction` of the Galois projection of `w` is trivial. The forward direction applies
   `abelianizationLift` of the continuous homomorphism
   `L.restriction ∘ localProjection EP ∘ (intermediateWeilEquiv F E)⁻¹`. By step 2 and
   `intermediateWeilEquiv_symm_projection`, this homomorphism kills the Weil subgroup of `M`.
   For the converse, steps 2 and `intermediateWeilEquiv_symm_projection` place the image of `w`
   in the Weil subgroup of `M`.
4. `mem_normSubgroup_iff`: for `x ∈ Eˣ`, `x ∈ normSubgroup EP.Carrier L.field` iff `x` is a
   norm from `Mˣ` (the range of `E.unitsNorm M`). This is
   `FiniteArtinTransport.mem_normSubgroup_map_iff` for the square of step 1.
5. Every element of the source of the inverse candidate is `e(mk w)` for a Weil element `w`.
   `Correspondence.finiteRestriction_reciprocityHom` identifies its finite restriction with
   `L.restriction` of the Galois projection of `w`. By definition of `e`, its value is
   `eC E (mk (intermediateWeilEquiv F E w))`
   (`intermediateReciprocityCandidate_projection`, by `rfl`).
   `ReciprocitySystemUniqueness.symm_mem_range_iff he.1.1` at `E ≤ M`, applied to `eC E a`,
   says that `a` lies in the range of `E.weilAbelianInclusion M` iff `eC E a` is a norm from
   `Mˣ`. Steps 3 and 4 then give the kernel equality.

## Final theorem

`intermediateGeometricProof` introduces `p`, `F`, `eC`, `he` and `E` and applies
`Correspondence.isGeometricReciprocity_of_localCandidate EP` to the pair
`⟨geometricOrder F E eC he.2, profiniteNormResidue F E eC he.1.1⟩`.

All helper declarations live in the namespace
`Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.IntermediateGeometric`. They are
internal steps of this proof; none is a new mathematical assertion beyond the cited Library
results. The target Lean/Markdown pair and its imports are unchanged.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
