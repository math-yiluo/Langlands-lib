# Automorphisms of an affine group over a number field acting on its adelic quotient

Module `Langlands.TraceFormula.AdelicGroupAutomorphism`. It supplies the twist `θ` of the
simple twisted trace formula in the Library's group-scheme framework. An automorphism `e` of
an affine group scheme `G` over a number field `F` gives a continuous automorphism of
`G(𝔸_F)`. It restricts to the norm-one subgroup `G(𝔸_F)^1` and preserves the principal
subgroup `G(F)`, so it descends to the quotient `G(F) \ G(𝔸_F)^1`. When `e` has finite order,
it preserves the Haar measure of `G(𝔸_F)^1` and the Library's quotient Haar measure. For
cyclic base change, the twist comes from the Galois group of `L / K` acting on the Weil
restriction `Res_{L/K} H_L`. The module builds this action and proves each such twist has
finite order.

## Source

Getz–Hahn, *An introduction to automorphic representations* (2024), §18.5, printed
pp. 486–488 (PDF page = printed + 7). There `θ` is a finite-order automorphism of a reductive
group `G` over a number field `F`. The operator `I_θ φ = φ ∘ θ⁻¹` acts on `L²([G])`
((18.33)), and the twisted trace formula is Corollary 18.5.1 (p. 488). Getz–Hahn use
`[G] = A_G G(F) \ G(𝔸_F)`. This module works on `G(F) \ G(𝔸_F)^1`, the Library's
`NormOneRationalQuotient`. Given a central split torus with the hypotheses of the Library's
`positiveQuotientHomeomorph` (`Global/AdelicSplitCenterQuotient.lean`), that map is a
homeomorphism from this quotient to `[G]`. This module does not
use that homeomorphism. Getz–Hahn assume finite order and use the induced quotient operator; they do not separately
prove these invariance properties in §18.5. The October 2026 author errata
(`getz-hahn-2024-errata-2026-10`, p. 4) correct only a cross-reference in this section.
This module proves the subgroup and measure invariance properties. The arguments are routine and are
not taken from the book:

- The adelic map is functorial in `e`.
- A continuous automorphism with a positive iterate equal to the identity has Haar
  character `1`.
- The Library's scaling theorem for compatible quotient measures applies.

## Generic lemmas (any locally compact group)

The definition `iterateEquiv` and its application lemma require a group `H` with a topology
and `φ : H ≃ₜ* H`. The Haar-character lemmas additionally assume `IsTopologicalGroup H`,
`LocallyCompactSpace H`, a measurable space and `BorelSpace H`. The final lemma assumes
`ρ.IsHaarMeasure` and `ρ.Regular`.

- `iterateEquiv φ k` is the `k`-fold composite. `iterateEquiv_apply` identifies it with
  `φ^[k]`. `mulEquivHaarChar_iterateEquiv`: its Haar character (Mathlib's `mulEquivHaarChar`)
  is `mulEquivHaarChar φ ^ k`.
- `mulEquivHaarChar_eq_one_of_iterate`: if `φ^[m] = id` for some `m ≠ 0`, then
  `mulEquivHaarChar φ = 1`.
- `measurePreserving_of_iterate`: under the same hypothesis, `φ` preserves every regular Haar
  measure `ρ` on `H`.

## Adelic automorphisms

Let `F` be a number field, `G : GroupScheme (Spec F)` and `e : Aut G`. The map on adelic
points is the Library's `AdelicGroupPoints.map F G G`.

- `map_comp_apply`, `map_id_apply`: `map` respects composition and identities pointwise.
- `adelicAut F e : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G` has forward map
  `map F G G e.hom` and inverse map `map F G G e.inv` (`adelicAut_apply`,
  `adelicAut_symm_apply`).
- `adelicAut_mul_apply`: `adelicAut F (e * e') = adelicAut F e ∘ adelicAut F e'`. In Mathlib's
  `Aut G`, the product `e * e'` applies `e'` first. Also `adelicAut_one_apply`, and
  `adelicAut_pow_apply` (`adelicAut F (e ^ k) = (adelicAut F e)^[k]`).
- `adelicAut_mem_normOneSubgroup_iff`: `adelicAut F e x ∈ G(𝔸_F)^1 ↔ x ∈ G(𝔸_F)^1`.
- `adelicAut_isOfFinOrder_iterate`: if `IsOfFinOrder e`, then some positive iterate of
  `adelicAut F e` is the identity.

## Norm-one group and rational quotient

- `normOneAut F e : normOneSubgroup F G ≃ₜ* normOneSubgroup F G` is the restriction of
  `adelicAut F e`, built with the Library's `QuotientIntegration.subgroupAutomorphism`. It
  agrees with the Library's `mapNormOne F G G e.hom`, and its inverse agrees with
  `mapNormOne F G G e.inv` (`normOneAut_val`, `normOneAut_symm_val`,
  `normOneAut_eq_mapNormOne`, `normOneAut_symm_eq_mapNormOne`). Also `normOneAut_pow_apply`.
- `normOneAut_mem_rationalNormOneSubgroup_iff`: `normOneAut F e` preserves the principal
  subgroup `rationalNormOneSubgroup F G`, the image of `G(F)`, in both directions.
- `rationalQuotientAut F e : NormOneRationalQuotient F G ≃ₜ NormOneRationalQuotient F G` is
  the Library's `QuotientIntegration.quotientAutomorphism` for this subgroup and `normOneAut F e`.
  It sends `G(F) x` to `G(F) e(x)`.

## Measure preservation (finite order)

These lemmas assume `[IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]` and `IsOfFinOrder e`.

- `measurePreserving_normOneAut`: `normOneAut F e` preserves `Measure.haar` on `G(𝔸_F)^1`.
- `measurePreserving_rationalQuotientAut`: with the additional instance hypothesis that
  `Measure.haar` on `G(𝔸_F)^1` is right invariant, `rationalQuotientAut F e` preserves the
  Library's `normOneRationalQuotientHaarMeasure F G`. The Library's `normOneHaarRightInvariant`
  proves right invariance for smooth connected `G`. The proof applies the Library's
  `IsCompatible.map_quotientAutomorphism` to the compatible triple (Haar measure, counting
  measure on `G(F)`, quotient measure). Both Haar characters in its scaling factor are `1` by
  `mulEquivHaarChar_eq_one_of_iterate`. The Library's
  `PositiveRealTorus.rationalNormOneSubgroup_count_isHaarMeasure` shows that counting measure on
  `G(F)` is a Haar measure.
- `measurePreserving_rationalQuotientAut_symm`: the same for the inverse map. This is the
  hypothesis `MeasurePreserving (quotientAutomorphism Γ θ hθ).symm ν ν` of the twisting operator
  `I_θ φ = φ ∘ θ⁻¹`, with `Γ = rationalNormOneSubgroup F G`, `θ = normOneAut F e` and
  `ν = normOneRationalQuotientHaarMeasure F G`.

## Galois twists of a Weil restriction

Let `L / K` be a finite field extension, `H` an affine group of locally finite type over `K`
and `σ : L ≃ₐ[K] L`.

- `weilGroup K L H` abbreviates the Library's Weil restriction
  `AffineWeil.groupScheme K L (AffineWeil.unitBaseChange K L H)`, that is, `Res_{L/K} H_L`.
- `unitGaloisPointHom_apply` unfolds the Library's coefficient conjugation on points.
  `unitGaloisTransformation_mul` and `unitGaloisTransformation_one` give the composition law
  of the corresponding natural transformations.
- `unitGaloisAction_mul`:
  `unitGaloisAction (σ * τ) = unitGaloisAction τ ≫ unitGaloisAction σ` (diagram order: `τ`
  first). Also `unitGaloisAction_one` (`= 𝟙`). Here `unitGaloisAction` is the Library's
  `AffineWeil.unitGaloisAction`. On points with values in `K`-algebras `A` it is conjugation
  by `σ` on the factor `L` of `L ⊗_K A` (`AffineWeil.unitGaloisAction_groundPoints`).
- `unitGaloisAut K L H σ : Aut (weilGroup K L H)` has forward map `unitGaloisAction σ` and
  inverse map `unitGaloisAction σ⁻¹` (`unitGaloisAut_hom`).
- `unitGaloisAutHom K L H : (L ≃ₐ[K] L) →* Aut (weilGroup K L H)` is a group homomorphism
  (`unitGaloisAutHom_apply`).
- `isOfFinOrder_unitGaloisAut`: every `unitGaloisAut K L H σ` has finite order, because
  `L ≃ₐ[K] L` is finite.

When `K` is a number field, the following two lemmas combine the Weil-restriction results
with the measure-preservation results:

- `measurePreserving_normOneAut_unitGaloisAut`: `normOneAut K (unitGaloisAut K L H σ)`
  preserves the Haar measure of `Res_{L/K} H_L(𝔸_K)^1`.
- `measurePreserving_rationalQuotientAut_unitGaloisAut_symm`: with Haar measure on that
  norm-one group right invariant, the inverse of the induced quotient map preserves
  `normOneRationalQuotientHaarMeasure K (weilGroup K L H)`.

## Scope

The module defines the twist and proves only the stated invariance properties. It does not
compare `Res_{L/K} H_L(𝔸_K)` with `H(𝔸_L)`, and it does not compare the twist with the Library's
entrywise Galois action on `GL_n` (`AdelicGLTransport.adelicEquiv`). It states no trace
formula.
