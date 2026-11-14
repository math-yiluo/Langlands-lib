# Primitivity of actual `H¹(A, 𝒪_A)` and the coproduct of cup products

Module `Langlands.AbelianScheme.CanonicalH1Primitive`.

## Purpose

This module proves the degree-one primitivity of structure-sheaf cohomology of
an abelian scheme over a field, and the resulting coproduct formula for cup
products of degree-one classes. Both concern the canonical pullbacks used by
`Langlands.AbelianScheme.FieldH2ExteriorCoproductComparisonStatement`. It
applies the Library's Čech primitivity
(`Langlands.Cohomology.Cech.exists_pull_sub_refine_eq_d`) through the ordered
Čech bridge (`CechResolution.AllSeqCup`).

## General facts (namespace `...CechResolution.AllSeq`)

- `cochainSecEquiv π U halg p`: suppose `R`-algebra structures on the rings of
  sections satisfy `halg : algebraMap R Γ(X, W) = (secHom π W).hom`. Then the
  identity map is an `R`-linear equivalence from
  `AllSeq.cochain π U (unitModule X) p` to the raw families
  `∀ σ : Fin (p + 1) → I, Γ(X, inter U σ)`. Both sides scale by the image of `r`
  in the sections (`AllSeq.smul_apply`, `Algebra.smul_def`).
  `cochainSecEquiv_dCochain` says that it carries `dCochain` to the Library's
  `Cech.d`.
- `isAffineOpen_inf_preimage πX m hV hW`: if `πX : X ⟶ Spec R` is separated,
  `V` is an affine open of `P`, and `W` is an affine open of `X`, then
  `V ⊓ m⁻¹ W` is affine. Proof: `V.ι ≫ m ≫ πX` is a map between affine schemes,
  so `V.ι ≫ m` is affine (`IsAffineHom.of_comp`). Hence `(V.ι ≫ m)⁻¹ W` is
  affine, and so is its image `V ⊓ m⁻¹ W` under the open immersion `V.ι`.

## Abelian schemes (namespace `Langlands.AbelianScheme`)

Fix a field `K` and `A : AbelianScheme (Spec K)`. Write `P = A.X ⨯ A.X`,
`p₁ = prod.fst`, `p₂ = prod.snd`, and `m = p₁ * p₂`. These are exactly the data
of `FieldH2ExteriorCoproductComparisonStatement`.

- `pullStructure A f n` is the `K`-linear map
  `(relativeCohomologyPullback f 𝒪 n ≫ (relativeCohomology Y.hom n).map (pullbackUnitIso f.left).hom).hom`.
  For `n = 2` and `f ∈ {p₁, p₂, m}` this is the statement's `pull f`.
- `pullStructure_mul`: `pullStructure A m 1 x = pullStructure A p₁ 1 x + pullStructure A p₂ 1 x`
  for every `x ∈ H¹(A, 𝒪_A)`.

  Proof. The square for `p₁, p₂` over `πX = A.X.hom` is a pullback
  (`Over.isPullback_of_binaryFan_isLimit`). The unit point is `e = η.left`. The
  axes are `(prod.lift (𝟙) (toUnit ≫ η)).left` and
  `(prod.lift (toUnit ≫ η) (𝟙)).left`. They satisfy `i ≫ m = 𝟙` by
  `MonObj.comp_mul` and the unit laws. Take a finite affine cover `U`
  (`exists_affineCover`) and the cover
  `W = primCover p₁ p₂ m U = p₁⁻¹ U a ⊓ p₂⁻¹ U b ⊓ m⁻¹ U c` of `P`. Its members
  are affine by `isAffineOpen_prodOpen` and `isAffineOpen_inf_preimage`, and
  `P.hom` is separated (base change of `πX`). Write `x` as the class
  `canonicalClass` of an ordered Čech cocycle `z`. By `pull_canonicalClass`,
  each pullback is the class of `Cech.pull` of `z` along the index maps
  `Prod.fst ∘ Prod.fst`, `Prod.snd ∘ Prod.fst`, and `Prod.snd`.
  `exists_pull_sub_refine_eq_d` gives `m^* z - (p₁^* z + p₂^* z) = d g` on `W`.
  Its hypotheses are: `K` is a field, global functions are constant
  (`surjective_secHom_top`), and the axis identities above. `Cech.refine_pull`
  rewrites the refinement. Then `canonicalClass_eq_zero_iff` gives the claim.
- Chosen covers: `coverIdx A` and `cover A` form a chosen finite affine cover
  (`Classical.choose` of `exists_affineCover`), with `cover_affine` and
  `cover_top`. `productCover A` is `primCover` of it on `P`, with
  `productCover_affine`, `productCover_top`, and the three containments
  `productCover_le_fst`, `productCover_le_snd`, and `productCover_le_mul`.
  `isPullback_prod` and `isSeparated_prod_hom` record the product facts.
- `cupA A` and `cupP A` are the cup products
  `AllSeq.cupCanonical` on `H¹(A, 𝒪_A)` and on `H¹(P, 𝒪_P)`, computed on
  `cover A` and `productCover A`. `cupA_swap` and `cupP_swap` give
  anticommutativity.
- `pullStructure_cupA`: for every `f : P ⟶ A.X` with an index map
  `β` such that `productCover A j ≤ f⁻¹ (cover A (β j))`,
  `pullStructure A f 2 (cupA A x y) = cupP A (pullStructure A f 1 x) (pullStructure A f 1 y)`.
  This is `AllSeq.pull_cupCanonical`.
- `pullStructure_mul_cupA`: for `x, y ∈ H¹(A, 𝒪_A)`,
  `m^*(cupA x y) = p₁^*(cupA x y) + cupP (p₁^* x) (p₂^* y) - cupP (p₁^* y) (p₂^* x) + p₂^*(cupA x y)`.
  Here `f^*` abbreviates `pullStructure A f`. The proof applies
  `pullStructure_cupA` to `m`, then `pullStructure_mul` to `x` and `y`, then
  bilinearity, then `pullStructure_cupA` to `p₁` and `p₂`, and finally
  `cupP_swap` for the term `p₂^* x ∪ p₁^* y`.

## Scope

This module does not construct the Künneth comparison of
`FieldH2ExteriorCoproductComparisonStatement`. It does not prove that `cupA` is
alternating, and it does not prove that the cup products are independent of the
chosen covers. It uses only the published Library results named above. In
particular, it uses none of the six representability and dual-scheme statements
excluded by Task 6105, and no proof of `FieldH2PrimitiveInjectivityStatement`.

## Provenance

This is internal infrastructure. Primitivity of degree-one classes of an abelian
variety is the statement that the Library module `CechPrimitive` cites from the
registered source `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
(6.12)–(6.15). This module transfers that Čech statement to actual cohomology.
The cup formula is a formal consequence of primitivity, naturality of the cup
product, and anticommutativity.
