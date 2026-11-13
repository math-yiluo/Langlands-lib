# The Weyl parameter of a geometric-lemma piece between two Levis

Module `Langlands.Representation.LanglandsClassification.CrossLeviPieceWeylParameter`.

## Purpose and provenance

This is derived content. It is an internal generalization of the published module
`UnramifiedPieceWeylParameter`, which treats two parabolics with a common Levi. Here the
two parabolics `P = MN` and `Q = LU` may have different Levis `M` and `L`. Renard VII.4.2
(ii) (David Renard, *Représentations des groupes réductifs p-adiques*, printed pp.244–246)
compares the exponents of `r_{Q}^G i_P^G(σ ⊗ ψ)` with the Weyl conjugates of the real
part of `ψ`. This module provides that comparison for the unramified part, as an
identity of real parameters. It transcribes no new assertion from the literature.

## Declarations

In namespace `Langlands.GroupScheme`:

- `exists_normalizerPoint_of_commonSplitTorus_two`. Let `j : M → G` and `jL : L → G` be
  closed connected reductive subgroups, and let `i : T → G` be a maximal split torus
  that factors as `iM : T → M` and as `iL : T → L`. Let `s : S → M` and `t : S → L` be
  maps whose composites into `G` are maximal split tori and satisfy
  `s ≫ j = t ≫ jL ≫ Inn(z)`. Then there are `mS ∈ M(k)`, `mT ∈ L(k)` and a normalizer
  point `n` of `i` with `n = j(mS) · z · jL(mT)⁻¹`. The proof applies rational
  maximal-split-torus conjugacy (`maximalSplitTorusConjugacy`) once in `M` and once in
  `L`. The composite torus isomorphism shows that the corrected point normalizes `i`.
  This is the proof of the published `exists_normalizerPoint_of_commonSplitTorus`, with
  the second subgroup changed to `L`.
- `comp_innerIso_eq_normalizer_pullback_two`. Let `a : A → L` be central with
  `f ≫ iL = a`, and let `b : A → M` satisfy `b ≫ j = a ≫ jL ≫ Inn(z)`. For `n` as above,
  `b ≫ Inn_M(mS) = (f ≫ σ_n) ≫ iM`, where `σ_n = normalizingAut i n`. Centrality of `a`
  in `L` removes `mT`. Cancellation uses the monomorphism `j`.
- `character_comp_eq_of_normalizerCorrection_two`. Consequently every character
  `χ : M(k) → ℂˣ` satisfies `χ ∘ b = χ ∘ ((f ≫ σ_n) ≫ iM)`, because `ℂˣ` is commutative.

In namespace `Langlands.Aubert.General.RepresentedParabolic.GeometricLemmaIntersectionDatum`:
let `D` be an intersection datum at `z` for `P = MN` and `Q = LU`. Let
`pres : ParabolicRootPresentation p l aM` be a presentation for `M`, with maximal split
torus `i = pres.data.i`, and let `iL : T → L` satisfy `iL ≫ lQ ≫ q = i`.

- `exists_normalizerPoint_crossLevi` applies the first lemma to the source common torus
  `D.t ≫ D.l' ≫ D.p'` (into `M`) and the target common torus
  `D.targetCommonTorusHom ≫ D.lQ' ≫ D.q'` (into `L`). It uses
  `D.targetCommonTorusHom_comp`, `D.isMaximalSplitTorus` and
  `D.targetCommonTorus_isMaximalSplitTorus_ambient`.
- `character_comp_piece_eq_normalizerPullback_crossLevi`. For a central `a : A → L` with
  `f ≫ iL = a`, and `b : A → L'` with `b ≫ D.lQ' ≫ D.q' = a`, characters of `M` agree on
  the piece map `b ≫ D.φ.hom ≫ D.l' ≫ D.p'` and on `(f ≫ σ_n) ≫ pres.leviTorusHom`. The
  equation `b ≫ φ ≫ l' ≫ p' ≫ l ≫ p = a ≫ lQ ≫ q ≫ Inn(z)` comes from `D.φ_comp`.
- `exists_normalizedRealPart_piece_eq_weyl_crossLevi` (main result). For a split
  component `a` of `L` and an unramified character `ψ` of `M(k)`, there is `w` in the
  relative Weyl group of `i` with

  ```
  normalizedRealPart (ψ ∘ (b ≫ D.φ.hom ≫ D.l' ≫ D.p'))
    = rationalCharacterRestrictReal f (relativeWeylFullRealAction i w ŷ),
  ```

  where `ŷ = leviUnramifiedFullRealPart pres ψ`. Here `w` is the class of `n⁻¹`. The
  proof is the same computation as the published
  `normalizedRealPart_piece_eq_of_normalizerCorrection`. It uses functoriality of
  normalized real parts (`normalizedRealPart_comp_points`) along `σ_n` and then along
  `f`, and uniqueness of normalizing automorphisms for `n⁻¹`.
