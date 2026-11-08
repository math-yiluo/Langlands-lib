# Tower embeddings into finite Galois intermediate fields of the closure

Author: Worker 1839, for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`. All
declarations are in `Langlands.Weil.Local.FiniteGaloisTower`. The tower theorem
`relativeInflation_finiteGaloisClass` of `FiniteGaloisTower` has the hypothesis
`hF1`: the published embedding of `L` into `\bar F` extends that of `E`. This
module produces, for every finite normal intermediate field `L₀` of the closure of
`F` that contains the image of `E`, an embedding `g : E → L₀` satisfying `hF1`. It
then specializes the tower theorem to that embedding.

## Setting

`F E : PadicField.{u} p`, `f : F.Carrier →ₐ[Padic p] E.Carrier`, and
`L₀ : FiniteIntermediateExtension F.Carrier` with `Normal F.Carrier L₀.field`.
`LP = L₀.asPadicField`, with the published `Padic p`-algebra structure on
`L₀.field`. The hypothesis
`hEL : extensionIntermediateField F E f ≤ L₀.field` says that `L₀` contains the
published image of `E`. Write `c = intermediateClosureCorrection F L₀` for the
published element of `G_F` with `c(emb_{L₀}(x)) = x`. Here `emb_{L₀}` is
`extensionFieldEmbedding F LP (intermediateEmbedding F L₀)`.

## Declarations

- `absoluteGalois_mem_of_normal`: every `σ ∈ G_F` maps `L₀` into itself. This is
  Mathlib's `IntermediateField.normal_iff_forall_map_le'`.
- `towerFieldEmbedding F E f L₀ hEL : E.Carrier →ₐ[Padic p] LP.Carrier` is
  `z ↦ c(emb_E z)`. Its values lie in `L₀` by `hEL` and the previous lemma.
  Linearity over `Padic p` holds because `emb_E (f x)` is the image of `x` in the
  closure and `c` fixes `F`.
- `towerFieldEmbedding_comp`: `g.comp f = intermediateEmbedding F L₀`, the literal
  inclusion of `F` into `L₀`.
- `towerFieldEmbedding_hF1`: for all `z`,
  `extensionFieldEmbedding F LP (g.comp f) (g z) = extensionFieldEmbedding F E f z`.
  After rewriting `g.comp f`, apply the injective `c`. The published
  `intermediateClosureCorrection_fieldEmbedding` turns the left side into `g z`,
  which is `c(emb_E z)` by definition.
- `extensionAlgebra_intermediateEmbedding`: the algebra given by the literal
  inclusion is the intermediate-field algebra (`Algebra.algebra_ext`).
- `towerFieldEmbedding_isGalois`: if `L₀/F` is Galois, then `LP` is Galois over
  `F` for `extensionAlgebra F LP (g.comp f)`. This follows by rewriting with the
  two previous lemmas.
- `relativeInflation_finiteGaloisClass_of_le`: the tower theorem for `L₀`. Under
  `hE`, `IsGalois F.Carrier L₀.field`, geometric candidates for `E` and `LP`, and
  `hT` (the published transfer–inclusion statement),

  `relativeInflation F E LP 2 (finiteGaloisClass F E f hE eE heE) =
    finrank E LP • finiteGaloisClass F LP (g.comp f) _ eL heL`.

## Provenance

Internal. The module is a construction from the published
`intermediateClosureCorrection`, `extensionFieldEmbedding` and
`extensionIntermediateField`, and from Mathlib's characterization of normal
intermediate fields. It makes no arithmetic claim beyond the tower theorem that it
specializes.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
