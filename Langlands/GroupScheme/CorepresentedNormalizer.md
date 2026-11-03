# Normalizers and centralizers of cut-out algebra-point subgroups

This module works over an arbitrary commutative ring `R`. It fixes a group-valued functor `F` on commutative `R`-algebras, corepresented by an algebra `B` through `e`, and a family of subgroups `H A ⊆ F A` cut out by an ideal `I` of `B` (`IsCutOutBy e H I`: `x ∈ H A` exactly when the classifying map `B ⟶ A` of `x` kills `I`).

## Families

- `normalizerFamily H A` is the subgroup of `g ∈ F A` such that, for every algebra map `f : A ⟶ A'` and every `x ∈ H A'`, both `F.map f g * x * (F.map f g)⁻¹` and `(F.map f g)⁻¹ * x * F.map f g` lie in `H A'`. This is the algebra-level form of Milne's normalizer functor, `N(R) = {g | g H(R') g⁻¹ = H(R') for all R-algebras R'}` (Proposition 1.83).
- `centralizerFamily H A` is the subgroup of `g` such that `F.map f g` commutes with every `x ∈ H A'`, after every algebra map `f : A ⟶ A'` (Milne, Proposition 1.92).

The subgroup axioms are checked directly. `mem_normalizerFamily` and `mem_centralizerFamily` unfold membership.

## Universal cut point

`tensorQuotient I A` is `A ⊗[R] (B ⧸ I)`, with inclusions `tensorQuotientLeft` and `tensorQuotientRight`. For `φ : B ⟶ A`, `tensorQuotientMap I φ` is `φ ⊗ id`. On elements it is `φ.rTensor (B ⧸ I)` (`tensorQuotientMap_apply`). `universalCutPoint e I A ∈ F (A ⊗[R] (B ⧸ I))` is the point classified by `B ⟶ B ⧸ I ⟶ A ⊗[R] (B ⧸ I)`.

- `universalCutPoint_mem`: the universal cut point lies in `H`.
- `exists_universalCutPoint`: every `x ∈ H A'` over an `A`-algebra `f : A ⟶ A'` is the image of the universal cut point under an algebra map `A ⊗[R] (B ⧸ I) ⟶ A'` restricting to `f` on `A`. This map is `Algebra.TensorProduct.lift f φ`, where `φ : B ⧸ I ⟶ A'` is induced by the classifying map of `x`.
- `homEquiv_symm_map`, `tensorQuotientLeft_comp_map`, `map_universalCutPoint` and `map_tensorQuotientLeft_universal` are naturality identities for base change along `φ : B ⟶ A`.

Consequently `mem_normalizerFamily_iff` and `mem_centralizerFamily_iff` show that the conditions need only be tested on the universal cut point over `A ⊗[R] (B ⧸ I)`.

## Ideals

Let `universalLeftPoint e I` be the universal point of `F` pulled back to `B ⊗[R] (B ⧸ I)`. `universalConjugate` and `universalInvConjugate` are its conjugates `g x g⁻¹` and `g⁻¹ x g` of the universal cut point `x`.

- `subgroupNormalizerIdeal e I` is the sum of the published coefficient ideals (`ProjectiveTensorCoefficients.coefficientIdeal`, along `B ⧸ I`) of the images of `I` under the classifying maps of the two universal conjugates.
- `subgroupCentralizerIdeal e I` is the coefficient ideal of the differences between the classifying maps of `g x` and `x g`, for the universal points `g` and `x`.

## Main results

Assume `B ⧸ I` is projective over `R`, as it always is over a field.

- `map_tensorQuotientMap_mem_iff`: the base change along `φ` of a point `y` over `B ⊗[R] (B ⧸ I)` lies in `H` exactly when `φ` kills the coefficient ideal of the image of `I` under the classifying map of `y`. The proof uses the published `coefficientIdeal_le_ker_iff`, which needs projectivity.
- `isCutOutBy_normalizerFamily`: `normalizerFamily H` is cut out by `subgroupNormalizerIdeal e I`.
- `isCutOutBy_centralizerFamily`: `centralizerFamily H` is cut out by `subgroupCentralizerIdeal e I`.

In both proofs a point `g ∈ F A` is written as `e.homEquiv φ`. Its universal conjugates (or the products for the centralizer) over `A ⊗[R] (B ⧸ I)` are the base changes along `φ ⊗ id` of the universal ones over `B ⊗[R] (B ⧸ I)`.

## Provenance

This is an internal construction toward task `0f453442` (smooth closed normalizers and centralizers of split tori). The statements are algebra-level forms of the normalizer and centralizer functors of Milne, *Algebraic Groups* (2017), Propositions 1.83 and 1.92. They are proved by a universal-point argument, not by Milne's transporter route. Milne reduces both propositions to the closed transporter of Proposition 1.79, which rests on closedness of `Mor(Y, Z)` in `Mor(Y, X)`. Here the universal cut point over `A ⊗[R] (B ⧸ I)` replaces the morphism functors, and vanishing of coefficients along the projective module `B ⧸ I` replaces the choice of a basis. No finiteness, smoothness or field hypothesis is used apart from projectivity of `B ⧸ I`.
