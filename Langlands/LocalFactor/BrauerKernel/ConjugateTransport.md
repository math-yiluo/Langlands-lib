# Reciprocity on a conjugate of the image of a standalone extension

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. At the distinguished
place of Deligne's global argument (1973, proof of Lemma 4.12), a generator field `L` of the
common closure of `F` is identified with a standalone p-adic field `E` (a completion of a number
field) by an `F`-embedding `b : E → \bar F` with image `L`. The published transport
`LocalClassField.extensionReciprocityCandidate F E f e` instead reads the family `e` on the image
`L''` of Mathlib's chosen embedding `Λ'' = extensionFieldEmbedding F E f`. The two embeddings differ
by a Galois element. This unit compares the reciprocity components of `e` on `L''` and on `L`
through the conjugation square of a normalized family. It is internal bookkeeping with the
published definitions and has no separate literature source.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. `F : PadicField.{uF} p`, `E : PadicField.{uE} p`
with independent universes, `f : F →ₐ[ℚ_p] E`, and `e : ReciprocityFamily F`. Standalone fields
carry their canonical topology (a local instance of this file).

## Results

- `reciprocityUnits_coe_eq_of_field_eq`: if two finite intermediate fields `A`, `B` have the same
  underlying field, the reciprocity components at equal Weil elements agree in the closure. Proof:
  `A = B` as subtypes; substitute.
- `reciprocityUnits_weilConjugation`: for normalized `e`, `M : Extension F` and `w ∈ W_F` with Galois
  projection `σ`, the component for `σ(M)` at `w x w⁻¹` is `σ` of the component for `M` at `x`. This
  is the conjugation square (`ConjugationRelation`, the third coherence clause of the normalized
  system relation) evaluated on the abelianization projection of `x`.
- `rankOne_reciprocityUnits_surjective`: the reciprocity map `W_E → E^×` of any rank-one candidate is
  onto (quotient projection followed by an equivalence).
- `reciprocityUnits_extensionImage`: for `y ∈ W_E`, the component of `e` for `L''` at the image of
  `y` is `Λ''` of the transported candidate at `y`. This is the definition of
  `extensionReciprocityCandidate` together with `extensionIntermediatePadicEquiv_coe`.
- `conj_extensionFiniteIntermediate_field`: if `b : E → \bar F` has image `L` and `w ∈ W_F` satisfies
  `σ(Λ'' x) = b x` for all `x`, then the conjugate `σ(L'')` has the same underlying field as `L`.
- `conj_extensionWeilMap_mem`: under that equality, `w y w⁻¹` lies in the Weil subgroup of `L` for
  every `y ∈ W_E` (published `conj_mem_pullbackFixingSubgroup`).
- `reciprocityUnits_conj_extension` (**reciprocity on a conjugate image field**): with normalized
  `e`, `w` as above and `y ∈ W_E`, the component of `e` for `L` at `w y w⁻¹` equals
  `b (rec_{e'} y)`, where `e' = extensionReciprocityCandidate F E f e`. Proof: by
  `reciprocityUnits_coe_eq_of_field_eq` pass to `σ(L'')`; apply the conjugation square and
  `reciprocityUnits_extensionImage`; finish with the hypothesis on `w`.
