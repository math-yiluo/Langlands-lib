# Normalized induction along an isomorphic represented parabolic

Author: Worker 1720. Module `Langlands.Representation.Exponents.IsoParabolicInduction`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

This module treats the degenerate case `P = G` of Renard's normalized parabolic
induction `i_P^G`. Renard defines it in VI.1.2 (printed pp.135–136 / PDF pp.141–142;
registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`) by
`i_P^G(τ, E) = Ind_P^G(τ ⊗ δ_P^{-1/2}, E)`. Its space consists of the functions
`f : G → E` with `f(mng) = δ_P^{-1/2}(m) τ(m) f(g)` (VI.1.2.3). When `P = M = G`, the
radical `N` is trivial, so `δ_P = 1` and `f(g) = τ(g) f(1)`. Evaluation at `1` is then an
isomorphism `i_G^G τ ≅ τ`. Renard uses this degenerate case without stating it
separately. It is a derived consequence of the published definitions and is needed for
the morphism dichotomy of Renard III.2.5 / VI.5.3 when a maximal Levi is all of `G`. The
Lean route follows the published `GeometricFullLeviTerm.leviFullInductionIso`, which
treats the same degenerate case inside a coarse Levi.

The represented-parabolic interface realizes `P` and `M` as group schemes with closed
immersions `p : P ⟶ G` and `l : M ⟶ P`. "P = G" means here that `p` is an
isomorphism of group schemes. We assume that `l` is an isomorphism too (`[IsIso l]`) for
the constructions. Section "Existence form" below shows that connected reductivity of
`G` supplies this, using the published `IsRationalLeviSubgroup.isIso_of_isIso_parabolic`.

## Generic lemmas

- `pointImage_eq_top_of_isIso j`: for an isomorphism `j : M ⟶ G` of group schemes, the
  image `pointImage j` of the rational point map is `⊤`. The point of `M` mapping to
  `x` is the image of `x` under `inv j`, by functoriality of `rationalPoints.map`.
- The private lemmas `closedNormalizerCharacter_eq_one_of_eq_bot` and
  `closedHalfCharacter_eq_one_of_eq_bot` are stated for a locally compact topological
  group `H` and a closed subgroup `N = ⊥`. They state that the published normalizer Haar
  modulus `HaarModulus.closedNormalizerCharacter N hN` and its half character
  `HaarModulus.closedHalfCharacter N hN K hKN` are `1`. Conjugation on the subsingleton
  `N` is the identity continuous multiplicative equivalence, whose Haar character is `1`
  (Mathlib's `mulEquivHaarChar_refl`). The half character is the square root of the
  modulus, so it is `1` as well. These are copies of the private helpers of
  `GeometricFullLeviTerm`, which cannot be imported.

## The point isomorphism

The rest of the module assumes `[TopologicalSpace k] [IsAffineHom G.X.hom]`. It puts the
canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G` (local
instance `isoParabolicAmbientPointTopology`), and `leviPointTopology l hl` on
`rationalPoints M`, as in the published `ArbitraryParabolicLeviPoints`.

For `p : P ⟶ G`, `l : M ⟶ P` with `[IsIso p] [IsIso l]`, `hp : IsParabolicSubgroup p` and
`hl : IsRationalLeviSubgroup l`,

`isoLeviPointsEquiv p l hp hl : rationalPoints M ≃ₜ* rationalPoints G`

is the published `leviPointsEquiv p l hp hl : M(F) ≃ₜ* pointImage (l ≫ p)` followed by
the inclusion of `pointImage (l ≫ p) = ⊤` into `G(F)`. Its inverse sends `g` to the
preimage of `⟨g, _⟩` under `leviPointsEquiv`. Both directions are continuous because
`leviPointsEquiv` is a homeomorphism and the inclusion of the subtype is an embedding.
`isoLeviPointsEquiv_apply` (simp, `rfl`) states that it is the point map
`rationalPoints.map (l ≫ p)`.

## The induction equivalence

Additionally assume `[T2Space k] [LocallyCompactSpace (rationalPoints G)]
[NonarchimedeanGroup (rationalPoints G)]`. Let `r : U ⟶ P` with
`hr : LeviSubgroup.IsGeometricUnipotentRadical r` and
`hmul : IsIso (subgroupMultiplication l r)` be the radical data of the published
`leviInductionFunctor p l r hp hr hl hmul`, and let `σ` be a smooth complex
representation of `M(F)` with carrier universe `v`.

- `isoParabolicInductionRepEquiv p l r hp hr hl hmul σ` is an equivalence of
  representations of `G(F)` (Mathlib's `Representation.Equiv`). It goes from the
  representation of `(leviInductionFunctor p l r hp hr hl hmul).obj σ`, Renard's
  `i_P^G σ`, to the representation of
  `SmoothRep.pullback (isoLeviPointsEquiv p l hp hl).symm σ`. In the latter, `g ∈ G(F)`
  acts on the carrier of `σ` as the preimage of `g` in `M(F)` does. It is the published
  `Induction.smoothInducedTopEquiv`, whose forward map is evaluation at `1`. Its inputs
  are as follows:
  - The parabolic image `pointImage p` is `⊤`, by the published
    `IsSemidirectDecomposition.parabolic_eq_top_of_levi_eq_top` applied to the literal
    semidirect decomposition `isSemidirectDecomposition_pointImage` with full Levi
    `pointImage (l ≫ p) = ⊤`.
  - The radical image `pointImage (r ≫ p)` is `⊥`, by the published
    `IsSemidirectDecomposition.unipotent_eq_bot_of_levi_eq_top`.
  - The inducing representation of `x ∈ pointImage p` acts by
    `δ^{1/2}(x) • A(projection x)`, where `A` is `σ` pulled back along
    `leviPointsEquiv.symm`. Here `δ^{1/2}(x) = 1` by the half-character lemma above, and
    `projection x = ⟨x, _⟩` by `projection_levi`, since `x` lies in the full Levi. So the
    inducing representation agrees with the action of `x` on the pullback along
    `isoLeviPointsEquiv.symm`.
  - The target action is smooth: it is the smoothness field of the published
    `SmoothRep.pullback`, which is proved there by `isSmooth_comp`.

  The construction uses `set_option maxHeartbeats 400000`. Elaborating the `refine`
  that unifies the carrier of `leviInductionFunctor`'s object with the published smooth
  induction needs more than the default 200000 heartbeats. The option is local to this
  declaration.
- `isoParabolicInductionEquiv p l r hp hr hl hmul σ :
  (leviInductionFunctor p l r hp hr hl hmul).obj σ ≃ₗ[ℂ] σ` is the underlying linear
  equivalence of `isoParabolicInductionRepEquiv`. The pullback keeps the carrier of `σ`.
  The result is a linear equivalence and not an isomorphism in `SmoothRep`, because the
  induction functor moves the carrier universe from `v` to `max u v`.
- `isoParabolicInductionEquiv_apply` states, by `rfl`, that it is evaluation at `1`:
  `Induction.eval (pointImage p) (inducingRepresentation …) f 1`.
- `isoParabolicInductionEquiv_map` states that it intertwines the action of the point
  `rationalPoints.map (l ≫ p) a` of `G(F)` on `i_P^G σ` with the action of `a ∈ M(F)` on
  `σ`. This combines the intertwining property of `isoParabolicInductionRepEquiv` at
  `isoLeviPointsEquiv p l hp hl a` with `symm_apply_apply`.

## Existence form

`exists_isoParabolicInductionEquiv` assumes `[IsIso p]` and `hG : IsConnectedReductive G`
but not `[IsIso l]`. It states that there is a linear equivalence
`T : (leviInductionFunctor p l r hp hr hl hmul).obj σ ≃ₗ[ℂ] σ` with
`T ((l ≫ p)(a) · f) = σ(a) (T f)` for all `a ∈ M(F)` and all `f`. The published
`IsRationalLeviSubgroup.isIso_of_isIso_parabolic` gives `IsIso l`: a rational Levi of a
connected reductive group is the whole group, because its unipotent radical is trivial.
Then `isoParabolicInductionEquiv` and `isoParabolicInductionEquiv_map` are the witness.

## Scope

Only the induction endpoint is treated. No statement about the normalized Jacquet
functor along an isomorphic parabolic is made here. No naturality in `σ` is stated. The
local compactness and nonarchimedean-group instances of `G(F)` are hypotheses, as in the
published represented-parabolic interface.
