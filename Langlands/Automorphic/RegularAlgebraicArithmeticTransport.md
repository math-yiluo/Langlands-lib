# Arithmetic transport of the regular algebraic type at infinity

This module proves that Clozel's regular algebraic type at infinity, as
defined in `Langlands.Automorphic.RegularAlgebraic` (Clozel 1990, Définitions
1.8 and 3.12), is invariant under arithmetic pullback along an isomorphism
`e : K ≃+* L` of number fields. The fields `K` and `L` live in independent
universes `uK` and `uL`, and the matrix rank `n` is arbitrary, including
zero. The archimedean transports used are the existing ones:

- `ArchimedeanGLTransport.mixedEquiv e`, the arithmetic transport
  `K ⊗ ℝ ≃+* L ⊗ ℝ` of the mixed coordinates, induced by
  `infiniteAdeleEquiv e`, and its entrywise version `matrixRealLinearEquiv n e`;
- `ArchimedeanLieTransport.envelopingEquiv n e`, the enveloping algebra
  isomorphism lifted from the complexified real Lie algebra isomorphism, and
  its restriction `centerEquiv n e` to the centers;
- `OperatorRealization.arithmeticComap e`, the image of a realization over `L`
  under pullback of automorphic functions, with
  `arithmeticComapEquiv_differential` intertwining the differential actions
  along `envelopingEquiv n e`.

The statements are transport of structure. They are not stated in Clozel's or
Harris's papers; they make precise that the regular algebraic condition
depends on a number field only up to isomorphism, with the embeddings and the
highest weights reindexed.

## Reindexing the embeddings

- `indexEmbedding K j : K →+* ℂ` is the complex embedding read off by an index
  `j : EmbeddingIndex K`: the chosen embedding `w.embedding` for `inl w` and
  `inr (w, false)`, and its conjugate for `inr (w, true)`.
  `embeddingComponent_mixedEmbedding` states
  `embeddingComponent K j (mixedEmbedding K a) = indexEmbedding K j a`.
- `conjFlip e w` is the Boolean `(w.comap e).embedding ≠ w.embedding ∘ e` for a
  place `w` of `L`; `boolXorEquiv c` is `b ↦ xor b c` as a permutation of
  `Bool`.
- `embeddingIndexEquiv e : EmbeddingIndex L ≃ EmbeddingIndex K` sends `inl w`
  to `inl` of the pulled-back place `infinitePlaceEquiv e w = w.comap e`, and
  `inr (w, b)` to `inr (w.comap e, xor b (conjFlip e w))`
  (`embeddingIndexEquiv_inl`, `embeddingIndexEquiv_inr`). Pullback preserves
  real and complex places (`isReal_infinitePlaceEquiv_iff`,
  `isComplex_infinitePlaceEquiv_iff`, from Mathlib's `isReal_comap_iff`).
- `indexEmbedding_comp` states
  `(indexEmbedding L j).comp e = indexEmbedding K (embeddingIndexEquiv e j)`.
  At a real place this is Mathlib's `comap_embedding_of_isReal`. At a complex
  place, `w.comap e = mk (w.embedding ∘ e)`, so by Mathlib's `embedding_mk_eq`
  the chosen embedding of the pulled-back place is `w.embedding ∘ e` or its
  conjugate (`embedding_infinitePlaceEquiv`). In the first case `conjFlip` is
  false and both indices keep their Boolean. In the second case the
  composite is not real, because `w` is complex; so `conjFlip` is true and the
  two indices of the place are exchanged.
- `embeddingComponent_mixedEquiv` states
  `embeddingComponent L j (mixedEquiv e x) = embeddingComponent K (embeddingIndexEquiv e j) x`
  for every `x : K ⊗ ℝ`. Both sides are continuous in `x`
  (`continuous_embeddingComponent`, `continuous_mixedEquiv`). The image of `K`
  is dense in `K ⊗ ℝ` (`denseRange_mixedEmbedding`, from Mathlib's weak
  approximation `InfiniteAdeleRing.denseRange_algebraMap` and the coordinate
  isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace`). On that image,
  `mixedEquiv_mixedEmbedding` (`mixedEquiv e (mixedEmbedding K a) =
  mixedEmbedding L (e a)`, from `infiniteAdeleEquiv_diagonal`) and
  `indexEmbedding_comp` give equality.

## Weights and generators

- `diagonalWeight_mixedEquiv`: for `μ : EmbeddingIndex L → Fin n → ℂ` and
  `d : Fin n → K ⊗ ℝ`,
  `diagonalWeight L n μ (mixedEquiv e ∘ d) = diagonalWeight K n μ' d` with
  `μ' k = μ ((embeddingIndexEquiv e).symm k)`. The proof rewrites each
  coordinate by `embeddingComponent_mixedEquiv` and reindexes the sum over
  embedding indices along `embeddingIndexEquiv e`.
- `matrixRealLinearEquiv_diagonal` and `matrixRealLinearEquiv_single`: entrywise
  transport of `diag(d)` is `diag(mixedEquiv e ∘ d)`, and of the matrix unit
  `single i j a` is `single i j (mixedEquiv e a)`.
- `envelopingEquiv_realGenerator`:
  `envelopingEquiv n e (realGenerator K n X) = realGenerator L n (matrixRealLinearEquiv n e X)`,
  from `envelopingEquiv_generator`, `complexLieEquiv_complexify` and the
  definition of `realLieEquiv`.

## Highest weights and infinitesimal characters

- `transportAnnihilator n e w`, for a vector `w` of a module
  `W : ModuleCat.{uL}` over `EnvelopingAlgebra L n`, is the left ideal
  `{a | envelopingEquiv n e a • w = 0}` of `EnvelopingAlgebra K n`.
- `isHighestWeightCharacter_comp_centerEquiv`: if `χ` is the infinitesimal
  character of highest weight `μ` for `L`, then `χ ∘ centerEquiv n e` is the
  infinitesimal character of highest weight `μ'` (as above) for `K`. The
  witness module is the cyclic quotient
  `EnvelopingAlgebra K n ⧸ transportAnnihilator n e w`, a module in the
  universe `uK` of `K`, as `IsHighestWeightCharacter K n` requires; its
  vector is the class of `1`. Two classes `[a]`, `[b]` agree exactly when
  `envelopingEquiv n e a • w = envelopingEquiv n e b • w`, and `a • [1] = [a]`.
  Hence `[1] ≠ 0` because `w ≠ 0`. The diagonal generators act on `[1]` by
  `diagonalWeight K n μ' d`, by `envelopingEquiv_realGenerator`,
  `matrixRealLinearEquiv_diagonal` and `diagonalWeight_mixedEquiv`. The
  strictly upper triangular generators kill `[1]` by
  `matrixRealLinearEquiv_single`. A central `z` acts on `[1]` by
  `χ (centerEquiv n e z)`, since `centerEquiv n e z` is
  `envelopingEquiv n e z`.
- `isRegularAlgebraicCharacter_comp_centerEquiv`: regular algebraic characters
  of `L` give regular algebraic characters of `K`. The integral weight
  `μ' k = μ ((embeddingIndexEquiv e).symm k)` is antitone at every index
  because `μ` is.
- `OperatorRealization.HasInfinitesimalCharacter.arithmeticComap`: if the
  center acts on `S` through `χ`, it acts on `S.arithmeticComap e` through
  `χ ∘ centerEquiv n e`. Every vector of the pullback is
  `S.arithmeticComapEquiv e g`. By `arithmeticComapEquiv_differential`, a
  central `z` acts on it as the pullback of `envelopingEquiv n e z` acting on
  `g`. That action is the scalar `χ (centerEquiv n e z)`, and the continuous
  linear equivalence commutes with scalars.
- `OperatorRealization.IsRegularAlgebraic.arithmeticComap` and
  `OperatorRealization.arithmeticComap_isRegularAlgebraic_iff`: the regular
  algebraic type is preserved by pullback; it is reflected by pulling back
  along `e.symm` and `arithmeticComap_symm_arithmeticComap`.
- `CuspidalOperatorRealization.arithmeticComap_isoClass_isRegularAlgebraic_iff`
  and `CuspidalOperatorRealization.IsoClass.arithmeticComap_isRegularAlgebraic_iff`:
  the same equivalence for the class of an actual irreducible cuspidal
  realization of rank `r + 1` and its arithmetic pullback, and for the descended
  pullback `IsoClass.arithmeticComap e` of cuspidal classes. Both use
  `isoClass_isRegularAlgebraic_iff` and `arithmeticComap_realization`.

## Source and provenance

L. Clozel, *Motifs et formes automorphes: applications du principe de
fonctorialité*, in *Automorphic Forms, Shimura Varieties, and L-functions*,
Vol. I, Perspectives in Math. 10, Academic Press, 1990, pp.77–159 (source
`clozel-milne-automorphic-forms-shimura-varieties-l-functions-i-1990`):
Définition 1.8 (pp.89–90, the class `Alg(n)`) and Définition 3.12 (p.111,
regularity), in the highest-weight formulation of
`Langlands.Automorphic.RegularAlgebraic`. The transport statements of this
module are derived: they follow from that formulation and from the Library's
arithmetic transports listed above, and are not stated in the source.
