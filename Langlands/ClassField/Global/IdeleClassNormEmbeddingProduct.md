# The idele-class norm as a product over embeddings

Helper module for the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.TransferNormCompatibilityStatement`
(task `d02b213c-6237-44c1-a667-4a8c19662bfe`). Let `F ⊆ K ⊆ E` be number fields with
`E / F` normal, and let `s i` be a finite family of `F`-automorphisms of `E` whose
restrictions to `K` are the `F`-embeddings `K → E`, each exactly once. The module proves
that the norm `C_K → C_F`, followed by the inclusion `C_F → C_E`, equals the product of the
`s i`-translates of the inclusion `C_K → C_E`. The extension `K / F` need not be Galois.
The published `ideleClassNormGaloisProduct` is the case `K = E`.

## Declarations

All are in the namespace `Langlands.ClassField.Global`. The fields `F`, `K` and `E` may
lie in independent universes.

- `algebraMap_norm_eq_prod_algHom` (theorem). Let `K / F` be finite separable, let `E / F`
  be normal, and let `Fintype (K →ₐ[F] E)` be given. For `x ∈ K`, the image of
  `Algebra.norm F x` in `E` is `∏ τ : K →ₐ[F] E, τ x`. Here `F`, `K` and `E` are arbitrary
  fields in a tower with `IsScalarTower F K E`.
- `algebraMap_norm_eq_prod_of_bijective` (theorem). With the same hypotheses on the
  fields, let `s : I → (E ≃ₐ[F] E)` be a finite family such that
  `i ↦ (s i).toAlgHom.comp (IsScalarTower.toAlgHom F K E)` is a bijection onto
  `K →ₐ[F] E`. Then the image of `Algebra.norm F x` in `E` is
  `∏ i, s i (algebraMap K E x)`.
- `ideleClassInclusion_ideleClassNorm_eq_prod_of_norm` (theorem). Let `F`, `K` and `E` be
  number fields with algebra maps `F → K`, `K → E` and `F → E`, and let `s : I → (E ≃ₐ[F] E)`
  be a finite family. Assume `hs`: the image of `Algebra.norm F x` in `E` is
  `∏ i, s i (algebraMap K E x)` for every `x ∈ K`. Then, for every `x ∈ C_K`,

  ```text
  ideleClassInclusion (ideleClassNorm x)
    = ∏ i, relativeIdeleClassAut F E (s i) (ideleClassInclusion x)   in C_E.
  ```

  Here `ideleClassNorm (K := F) (L := K) : C_K → C_F` and the two `ideleClassInclusion`
  maps `C_F → C_E` and `C_K → C_E` are the published constructions.
- `ideleClassInclusion_ideleClassNorm_eq_prod` (theorem). The same identity for number
  fields `F ⊆ K ⊆ E` with `IsScalarTower F K E` and `Normal F E`. The hypothesis is that the
  restrictions of the `s i` to `K` are exactly the `F`-embeddings, as in
  `algebraMap_norm_eq_prod_of_bijective`.

The private lemmas are `denseRange_finiteCompletionProduct`,
`finiteNormComponent_principal'`, `finite_coordinate`, `infinite_part` and `adele_part`.

## Provenance

The field identity is the standard formula for the norm as a product over embeddings into a
normal closure. The idele-class identity is the norm formula used in Tate (1979),
*Number theoretic background*, (1.2.2), for the tower `F ⊆ K ⊆ E`. These are derived
internal lemmas for the target proof. The private lemma
`denseRange_finiteCompletionProduct` repeats, word for word, the private lemma of the same
name in `Langlands/Global/AdelicFunctoriality/IdeleClassNormTowerProof.lean`. The
private lemma `finiteNormComponent_principal'` repeats that module's private
`finiteNormComponent_principal`. They are copied because private declarations cannot be
imported.

## Implemented proof

### The field identity

`algebraMap_norm_eq_prod_algHom` works in `Ω = AlgebraicClosure E`. Let `ι : E → Ω` be the
algebra map. Composition with `ι` is a bijection from `K →ₐ[F] E` to `K →ₐ[F] Ω`.

- It is injective because `ι` is injective.
- For surjectivity, extend an embedding `ρ : K → Ω` to `φ : E → Ω` over `F`
  (`IsAlgClosed.surjective_domRestrict_of_isAlgebraic`; `E / K` is algebraic because
  `E / F` is). The automorphism `φ.restrictNormal' E` of `E` satisfies
  `ι ∘ φ.restrictNormal' E = φ` (`AlgHom.restrictNormal_commutes`), because `E / F` is
  normal. Its restriction to `K` maps to `ρ`.

Mathlib's `Algebra.norm_eq_prod_embeddings` writes the image of the norm in `Ω` as the
product over `K →ₐ[F] Ω`. Reindexing along the bijection and cancelling the injective `ι`
gives the formula. `algebraMap_norm_eq_prod_of_bijective` reindexes once more, along the
bijection `i ↦ (s i)|_K`. That bijection also supplies the `Fintype` instance.

### The adelic identity

The section `IdeleClass` takes the field identity as the hypothesis `hs`. It proves the
formula on adeles, coordinate by coordinate, by density of principal elements. The
argument follows the pattern of the published `IdeleClassNormGaloisProductProof` and
`IdeleClassNormTowerProof`.

- *Weak approximation.* `denseRange_finiteCompletionProduct` says that `K` is dense in the
  unrestricted product of all its finite completions. On a finite set of places this is
  Mathlib's `AbsoluteValue.denseRange_algebraMap_pi`, combined with density of `K` in each
  completion. A basic open set of the product constrains only finitely many coordinates.
- *A finite coordinate.* Fix a finite place `q` of `E`. `finite_coordinate` compares two
  continuous maps from `∏_w K_w` (all finite places `w` of `K`) to `E_q`.
  - Apply `finiteNormComponent` at `q.under (𝓞 F)`, then the completed inclusion
    `FiniteExtension.completionMap` into `E_q`.
  - For each `i`, let `q_i = finitePlaceEquiv (s i) q`. Take the coordinate at
    `q_i.under (𝓞 K)`, map it into `E_{q_i}` by the completed inclusion, transport it to
    `E_q` by `finiteCompletionEquiv (s i) q`, and multiply over `i`.

  The first map is continuous by `FiniteExtension.continuous_completionMap` and
  `continuous_finiteNormComponent`. The second is continuous by
  `continuous_finiteCompletionEquiv`. On diagonal elements `x ∈ K`, the first map gives
  the image of `Algebra.norm F x`. This is `finiteNormComponent_principal'`, a coordinate
  of the published `adeleNorm_principal`. The completed maps send diagonal elements to
  diagonal elements (`FiniteExtension.completionMap_coe`, `finiteCompletionEquiv_coe`),
  so `hs` gives equality there. `DenseRange.equalizer` then gives equality on the whole
  product.
- *Infinite part.* `infinite_part` is the same argument on `InfiniteAdeleRing K`. It uses
  `InfiniteAdeleRing.denseRange_algebraMap`, the first component of `adeleNorm_principal`,
  `infiniteAdeleMap_diagonal` and `infiniteAdeleEquiv_diagonal`.
- *Adeles.* `adele_part` combines the two parts by `Prod.ext` and `FiniteAdeleRing.ext`.
  The projections and the evaluation at `q` are monoid homomorphisms, so they commute with
  the finite product (`map_prod`). The `q`-coordinates of `finiteAdeleInclusion` and
  `finiteAdeleEquiv` are, by definition, the expressions in `finite_coordinate`.

### Ideles and idele classes

`ideleClassInclusion_ideleClassNorm_eq_prod_of_norm` chooses an idele representative
(`QuotientGroup.induction_on`) and rewrites with `ideleClassNorm_mk` and
`ideleClassInclusion_mk`. On ideles, `Units.ext` reduces the formula to the underlying
adeles, and `adele_part` proves it there. The quotient map is a monoid homomorphism, so it
commutes with the product. Finally, `ideleClassInclusion_ideleClassNorm_eq_prod` supplies
`hs` from `algebraMap_norm_eq_prod_of_bijective`. Number fields have characteristic zero,
so `K / F` is finite separable.
