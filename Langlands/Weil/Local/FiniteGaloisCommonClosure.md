# A finite Galois common closure with an unramified extension of the same degree

Author: Worker 1556, for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`. It builds on
Worker 1839's `FiniteGaloisTowerConstruction`. All declarations are in
`Langlands.Weil.Local.FiniteGaloisTower`.

For a finite Galois extension `E/F`, this module gives a finite unramified Galois
intermediate field `M₀` of the closure of `F` with `[M₀ : F] = [E : F]`. It also
gives a finite Galois intermediate field `L₀` that contains the published images of
both `E` and `M₀`. The tower lemma `relativeInflation_finiteGaloisClass_of_le` can
then be applied to `F ⊂ E ⊂ L₀` and to `F ⊂ M₀ ⊂ L₀`. The two tower embeddings
have the same degree `[L₀ : E] = [L₀ : M₀]`.

## Setting

`F E : PadicField.{u} p` and `f : F.Carrier →ₐ[Padic p] E.Carrier`, with the
algebra `extensionAlgebra F E f`. `extensionDegree F E f` is `[E : F]` for that
algebra. For `M : FiniteIntermediateExtension F.Carrier`, `MP = M.asPadicField` is
`M.field` with its published `Padic p`-structure. `intermediateEmbedding F M` is
the literal inclusion `F → M.field`. `extensionIntermediateField F E f` is the
published image of `E` in `AlgebraicClosure F.Carrier`.

## Declarations

- The imported `Langlands.PadicField.extensionDegree_intermediateEmbedding`
  from `Galois/Local/TotallyRamifiedSolvabilityProof`: `extensionDegree F MP
  (intermediateEmbedding F M) = finrank F M.field`. The proof rewrites with the
  published `extensionAlgebra_intermediateEmbedding`.
- `intermediateEmbedding_isGalois`: if `M.field/F` is Galois, then `MP` is Galois
  over `F` for the algebra of the literal inclusion.
- `extensionIntermediateField_intermediateEmbedding_le`: for normal `M`, the
  published image of `MP` under the literal inclusion lies in `M.field`. Each image
  point is `c⁻¹(x)` with `c = intermediateClosureCorrection F M` and `x ∈ M`, by
  `intermediateClosureCorrection_fieldEmbedding`. Normality makes `M` stable under
  `c⁻¹` (`absoluteGalois_mem_of_normal`).
- `extensionIntermediateField_isGalois`: if `E/F` is Galois for
  `extensionAlgebra F E f`, its image field is Galois over `F`. It is
  `F`-isomorphic to `E` by `extensionIntermediateFieldEquiv`.
- `towerFieldEmbedding_finrank_mul`: for normal `L₀` and `hEL` (the image of `E`
  lies in `L₀`), `[LP : E] · [E : F] = [L₀ : F]`. Here `E` acts on `LP` through
  `towerFieldEmbedding F E f L₀ hEL`. The scalar tower `F → E → L₀` uses the
  intermediate-field algebra on `L₀`. It commutes by `towerFieldEmbedding_comp`.
  The proof then applies Mathlib's `Module.finrank_mul_finrank`.
- `towerFieldEmbedding_finrank_eq`: if two such subextensions `E` and `E'` of `L₀`
  have `[E : F] = [E' : F]`, then `[LP : E] = [LP : E']`. This follows from the
  previous lemma and `extensionDegree_pos`.
- `commonClosure F E f M : FiniteIntermediateExtension F.Carrier` (definition) is
  the compositum `extensionIntermediateField F E f ⊔ M.field` in the closure.
  `commonClosure_field` states this, by `rfl`.
  `extensionIntermediateField_le_commonClosure` and
  `intermediateField_le_commonClosure` are the two inclusions.
- `commonClosure_isGalois`: if `E/F` is Galois and `M.field/F` is Galois, the
  compositum is Galois over `F`. This is Mathlib's instance for the supremum of
  two Galois intermediate fields.
- `exists_unramified_commonClosure`: if `E/F` is Galois, there exist
  `M₀ L₀ : FiniteIntermediateExtension F.Carrier` such that:
  - both `M₀.field` and `L₀.field` are Galois over `F`;
  - `F.canonicalTopologicalData.ramificationIndex =
    M₀.asPadicField.canonicalTopologicalData.ramificationIndex`;
  - `extensionDegree F M₀P (intermediateEmbedding F M₀) = extensionDegree F E f`;
  - `extensionIntermediateField F E f ≤ L₀.field`;
  - `extensionIntermediateField F M₀P (intermediateEmbedding F M₀) ≤ L₀.field`.

  `M₀` comes from the published `unramifiedExtensionDegreeExistence` at
  `n = [E : F]`. `L₀` is `commonClosure F E f M₀`. The last inclusion combines
  `extensionIntermediateField_intermediateEmbedding_le` with
  `intermediateField_le_commonClosure`.

## Provenance

Derived. These are standard facts: unramified extensions of every degree exist,
and the compositum of two Galois extensions is Galois. No new literature is cited;
the existence of unramified extensions is the published Library theorem. The module
uses the published
`unramifiedExtensionDegreeExistence`, `extensionIntermediateFieldEquiv`,
`intermediateClosureCorrection_fieldEmbedding` and `extensionAlgebra_intermediateEmbedding`.
It also uses Worker 1839's accepted `towerFieldEmbedding`, `towerFieldEmbedding_comp`
and `absoluteGalois_mem_of_normal`, and Mathlib's tower law and Galois compositum
instance. The module states no class identity and no reciprocity statement.
