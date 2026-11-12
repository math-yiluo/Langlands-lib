# The normalizer of a smooth connected subgroup is cut out by a finitely generated ideal

This helper module of `Langlands.GroupScheme.smoothConnectedNormalizer`
proves the algebraic heart of the affine case.

## Setting

`F` is a group functor on commutative `R`-algebras corepresented through `e` by
`B`. `H` is a family of subgroups cut out by an ideal `I` of `B`
(`IsCutOutBy e H I`, Library). The Library's `normalizerFamily H` is the
all-test normalizer: `g` over `A` belongs to it when, after every algebra map
`A → A'`, conjugation by `g` and by `g⁻¹` preserves `H A'`. By the Library's
`mem_normalizerFamily_iff`, this is equivalent to two conditions on the
universal cut point over `A ⊗[R] (B ⧸ I)`. Its conjugate by `g` (`conjPt`)
must lie in `H`, and so must its conjugate by `g⁻¹`.

Throughout, `B ⧸ I` is smooth over `R`, `I` is finitely generated, and every
`K ⊗[R] (B ⧸ I)` over a field `K` has connected prime spectrum.

## Main results

- `isCutOutBy_smoothNormalizerIdeal`: `normalizerFamily H` is cut out by the
  ideal `smoothNormalizerIdeal hI`.
- `smoothNormalizerIdeal_fg`: this ideal is finitely generated.

## Construction

Let `J` be the augmentation ideal of `B ⧸ I` (`augIdeal`), the kernel of the
counit of the cut subgroup. By the Library result
`Algebra.Smooth.finite_projective_quotient_ker_pow`, every truncation
`(B ⧸ I) ⧸ J ^ (n + 1)` is finite projective over `R`. `truncMap hI A n` is the
induced map `A ⊗[R] (B ⧸ I) → A ⊗[R] ((B ⧸ I) ⧸ J ^ (n + 1))`.

`normalizerIdealStep hI n` is the Library `coefficientIdeal`, along this
finite projective module, of the truncated images of `I` under the classifying
maps of the two universal conjugates (`universalConjugate`,
`universalInvConjugate`). `smoothNormalizerIdeal hI` is the supremum over all
`n`.

## Proofs

*Each step.* By the Library's `coefficientIdeal_le_ker_iff`, a point `g` of
`F` classified by `φ : B → A` kills `normalizerIdealStep hI n` exactly when
both conjugates of the universal cut point by `g` and by `g⁻¹` vanish on `I`
modulo `J ^ (n + 1)` (`normalizerIdealStep_le_ker_iff`). Thus `g` kills the
whole ideal exactly when both conjugates vanish on `I` modulo every power of
the augmentation ideal.

*Key lemma (`conjPt_mem`).* If the conjugate by `g` vanishes on `I` modulo
every power, then it lies in `H`. Over `A`, the family `conjFamily hI g` of
points `h` of the cut subgroup with `g h g⁻¹ ∈ H` is cut out by the image `K`
of `I` under the classifying map of `conjPt` (`isCutOutBy_conjFamily`). This
uses the base-change corepresentation `A ⊗[R] (B ⧸ I)` of `BaseChange`. `K` is
finitely generated. The kernel of the truncation lies in the matching power of
the augmentation ideal of the base change (`ker_truncMap_le`), so `K` lies in
every power. The fibres of `A ⊗[R] (B ⧸ I)` over `A` are fibres of `B ⧸ I` over
`R` (`connectedSpace_baseChange`), hence connected. `eq_bot_of_forall_le_pow` of
`OpenSubgroup` gives `K = ⊥`, which says exactly that the conjugate lies in `H`.

*Cut-out.* If `g` lies in the normalizer, both conjugates lie in `H`. They
therefore vanish on `I`, in particular modulo every power. Conversely, the key
lemma applied to `g` and to `g⁻¹` (`conjPt_inv`) gives both conjugates in `H`.

*Finite generation.* Each step is finitely generated: by
`coefficientIdeal_image_span`, the images of `I` may be replaced by the images
of a finite generating set. By `coefficientIdeal_fg`, the coefficient ideal of
finitely many tensors along a finite projective module is finitely generated.
For the whole ideal, the quotient point `B → B ⧸ smoothNormalizerIdeal hI`
lies in the normalizer by the cut-out property. Hence the two universal
conjugates, applied to each of the finitely many generators of `I`, lie in the
extension of `⨆ n, normalizerIdealStep hI n`. Each such membership involves
only finitely many steps, so the extension of a finite partial supremum `N'`
already contains them. The quotient point `B → B ⧸ N'` then lies in the
normalizer, so `smoothNormalizerIdeal hI ≤ N'`, and `N'` is finitely generated.

## Provenance

This is the finite-presentation and representability part of Brian Conrad,
*Reductive group schemes* (2014), Proposition 2.1.6 (printed and one-based
PDF pp.61–63, source `conrad-2014-reductive-group-schemes`). There the
normalizer is the intersection of the transporters of the infinitesimal
neighbourhoods of the identity section, each represented by a finitely
presented closed subscheme. The formal route is derived: it uses the
coefficient ideals of the Library's `ProjectiveTensorCoefficients` along the
finite projective jet modules. Finite generation of the supremum follows from
the cut-out property directly, without Noetherian approximation.
