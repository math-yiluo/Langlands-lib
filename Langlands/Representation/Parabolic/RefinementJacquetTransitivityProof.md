# Natural transitivity of the normalized upper Jacquet quotients

Author: Worker 834.

`Langlands.Parabolic.normalizedRefinementJacquetTransitivity` proves the
unchanged Library proposition
`Langlands.Parabolic.NormalizedRefinementJacquetTransitivityClause.{uF,uV} F T B S`
of `Langlands.Representation.Parabolic.RefinementTransitivityStatement`.
The theorem has the statement's binders exactly:
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`
`{n : ℕ} (B : BlockShape n) (S : BlockRefinement B)`, with independent
universes `uF` and `uV`. It adds no hypothesis. In particular it covers
rank zero, empty block shapes and empty refinements, and every object of
the canonical category of smooth complex representations of
`GL_n(F)` with carrier in `Type uV`. Admissibility, finite length,
irreducibility and nonzero rank are not assumed.

## Notation

Fix `B`, `S` and a representation `ρ` of `G = GL_n(F)` on `V`. Write
`M = B.Levi F.Carrier` and `L = refinedLevi F.Carrier B S`. Write `U₀`
for the outer radical `B.unipotentRadical F.Carrier` inside
`B.parabolic F.Carrier`, `U₁` for the inner radical
`refinedUnipotent F.Carrier B S ≤ M`, and `U` for the full radical
`composedUnipotent F.Carrier B S ≤ G`. By definition `U` is the
published `leviPreimage F.Carrier B U₁`: it consists of the matrices of
the upper block parabolic whose projection to `M` lies in `U₁`.

The three quotients are the published ones. `B.jacquetMk ρ` maps `V`
onto the outer quotient `B.JacquetModule ρ`. It carries the action
`T.normalizedJacquet B ρ` of `M`. The map `refinedJacquetMk B S` then
takes this quotient onto the inner quotient `RefinedJacquetModule`.
`composedJacquetMk B S ρ` maps `V` onto the full quotient
`ComposedJacquetModule B S ρ`. Write `[[v]]` for the iterated class
`refinedJacquetMk B S (T.normalizedJacquet B ρ) (B.jacquetMk ρ v)` and
`[v]` for the class `composedJacquetMk B S ρ v`.

## The inner radical acts trivially on scalars

`normalizedJacquet_refinedUnipotent` proves that every `u ∈ U₁` satisfies

```text
T.normalizedJacquet B ρ u (B.jacquetMk ρ v) = B.jacquetMk ρ (ρ(leviEmbedding u) v).
```

The proof rewrites with the published representative formula
`T.normalizedJacquet_mk_eq_inv_halfModulus`. That formula has the
scalar `T.leviHalfModulus B u` raised to the power `-1`. The published
lemma `T.leviHalfModulus_refinedUnipotent` makes this scalar equal to
one.

## The forward map

`firstMap` applies `Jacquet.lift` to the full class map
`composedJacquetMk B S ρ`, descending it through the outer quotient. It
is invariant under `U₀` because each `u ∈ U₀` has the same underlying
matrix as `radicalInPreimage F.Carrier B U₁ u ∈ U`. Thus
`firstMap(B.jacquetMk ρ v) = [v]`.

`forward` applies `Jacquet.lift` a second time, descending `firstMap`
through the inner quotient of `T.normalizedJacquet B ρ`. Invariance is
checked on outer classes, which suffices by `B.jacquetMk_surjective`.
For `u ∈ U₁`, the preceding lemma removes the normalizing scalar. The
embedded matrix `leviEmbedding u` is the value of
`preimageSection F.Carrier B U₁ u`, so it lies in `U` and the full
quotient map does not see it. Both descents compute on representatives
by definition, so `forward_mk` gives

```text
forward [[v]] = [v]        for every v ∈ V.
```

## The inverse map

`iteratedMk` is the composite of the two quotient maps `V → [[V]]`.
`iteratedMk_invariant` proves that it is invariant under `U`. Each
`g ∈ U` lies in `leviPreimage F.Carrier B U₁`. The published
factorization `preimageDecomposition` writes `g` as
`u · leviEmbedding(m)`, where `u ∈ U₀` is
`preimageUnipotentPart g` and `m ∈ U₁` is `preimageProjection g`. The
outer quotient map is invariant under `u`, by `Jacquet.mk_apply_subgroup`
for the restricted parabolic representation. Read backwards, the lemma
above identifies `B.jacquetMk ρ (ρ(leviEmbedding m) v)` with the action
of `m` on an outer class. The inner quotient map is invariant under
that action. `backward` descends `iteratedMk` through the full quotient
with `Jacquet.lift`, so `backward [v] = [[v]]`.

`backward_forward` and `forward_backward` prove that the two maps are
mutually inverse. Both quotient maps are surjective, so it is enough to
check representatives, where both identities hold by definition.

## Refined-Levi action and normalization

`forward_action` checks that `forward` intertwines the two normalized
actions of `L` on a class `[[v]]`. Let `m ∈ L` and write `e(m)` for the
matrix `B.leviEmbedding F.Carrier m`. On the iterated side, the
published formulas `T.normalizedRefinedJacquet_mk` and
`T.normalizedJacquet_mk_eq_inv_halfModulus` give

```text
refinedLeviInverseHalfModulus(m) · leviHalfModulus(m)⁻¹ · [[ρ(e(m)) v]].
```

The direct action, by `T.normalizedComposedJacquet_mk`, is

```text
inverseHalfCharacter(composedLeviModulus)(m) · [ρ(e(m)) v].
```

The published identity `T.inverseHalf_composedLeviModulus` rewrites the
direct scalar as `refinedOuterHalfModulus(m)⁻¹ · refinedLeviInverseHalfModulus(m)`.
`T.refinedOuterHalfModulus_apply` identifies `refinedOuterHalfModulus(m)`
with `leviHalfModulus(m)`. After `forward_mk`, linearity and
commutativity of complex multiplication, the two sides agree.

The direct normalization is thus the product of the outer inverse half,
restricted to `L`, and the inner inverse half. `forward_comp` extends
`forward_action` to all elements: it applies the extensionality
principle `Representation.Coinvariants.hom_ext` to both quotients.
`transitivityEquiv` packages `forward` and `backward` as a
`Representation.Equiv` between the actual representations
`T.normalizedRefinedJacquet B S (T.normalizedJacquet B ρ)` and
`T.normalizedComposedJacquet B S ρ`. Its forward function is literally
`forward`, which gives the value formula of `transitivityEquiv_mk`.

## Naturality and the final theorem

`transitivityIso` is `NatIso.ofComponents`, applied to
`SmoothRep.mkIso (transitivityEquiv T B S A.representation)` for each
smooth representation `A`. The source functor is
`T.normalizedJacquetFunctor B ⋙ T.normalizedRefinedJacquetFunctor B S`
and the target is `T.normalizedComposedJacquetFunctor B S`.

Naturality is checked for every morphism `f : A ⟶ A'` of smooth
representations. After extensionality and surjectivity of both quotient
maps, it suffices to evaluate both composites on `[[v]]`. The functors'
actual morphism maps are the descended maps
`B.normalizedJacquetOfMap`, `normalizedRefinedJacquetOfMap` and
`T.normalizedComposedJacquetMap`. Each sends a class of `v` to the class
of `f v`. Both sides therefore equal `[f v]` by definitional unfolding.

`normalizedRefinementJacquetTransitivity` returns this natural
isomorphism. The required formula
`SmoothRep.hom (E.hom.app A) [[v]] = [v]` holds by definition. Every
component of `E` is the categorical isomorphism determined by the
equivariant linear equivalence above. Invertibility, refined-Levi
equivariance with inverse-half normalization, and naturality are
therefore part of the proved conclusion. The theorem assumes none of
them. The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Scope

The target is the intrinsic quotient by the actual full radical
`composedUnipotent`. No abstract quotient or replacement statement is
introduced. The theorem compares this quotient only with the iterated
quotients of the published functors. Comparison with flattened block
coordinates is a separate obligation and is not proved here. So is the
identification of the explicit determinant-norm moduli with Haar-measure
moduli. The induction conjunct of `NormalizedRefinementTransitivityStatement`
is not touched here.

## Sources

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ÉNS
(4) **10** (1977), ID `bernstein-zelevinsky-1977-induced-i`. Retained
file:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`
(verified). The following passages were read from that file:

- Section 1.8(b), printed p.444 (PDF p.5). The Jacquet functor
  `r_{U,θ}` is the quotient `E/E(U,θ)`, and `M` acts by
  `mod_U^{-1/2}(m) · (π(m)ξ + E(U,θ))`. The exponent `-1/2` was confirmed
  on a rendered scan of the page, because the text layer drops the minus
  sign. This is the inverse-half convention of the Lean functors, here
  with trivial `θ`.
- Proposition 1.9(c), printed p.445 (PDF p.6). It states
  `r_{V,θ'} ∘ r_{U,θ} = r_{U°,θ°}` for `U° = UV`. The remark after the
  proposition says that the normalizing factors must be checked to be
  compatible. In this proof that check is the scalar identity of the
  section on refined-Levi action.
- Sections 2.1–2.2 and Proposition 2.3(c), printed p.446 (PDF p.7).
  These specialize to standard Levi subgroups of `GL_n` indexed by
  ordered partitions, which correspond to block refinements. They state
  `r_{N,M} ∘ r_{M,G} = r_{N,G}` for `N < M < G`.

No errata for BZ77 are recorded in the Library notes or in the project
literature folder. The proof follows the source's route: two successive
coinvariant quotients, the factorization `U = U₀ · e(U₁)` and
compatibility of the normalizing characters. The concrete class formula
`[[v]] ↦ [v]`, the categorical naturality, the arbitrary carrier
universe and the inclusion of empty or rank-zero cases are derived
formulations of the published statement, not quotations from the
source. The source states transitivity for reductive groups with Haar
moduli. The Lean statement uses the explicit block moduli of the
published constructions, and the proof uses only their published product
identities.

## Dependency audit

The module imports only the target statement module
`Langlands.Representation.Parabolic.RefinementTransitivityStatement`.
That module and its transitive Library imports are 55 `Langlands`
modules. These are the basic group, modulus, smooth-representation,
twist, coinvariant, induction, Jacquet and refinement modules. They also
include the definition modules
`Langlands.Representation.Classification.Supercuspidal` and
`SupercuspidalTwist`, which `RefinementCharacter` imports for twisting
definitions. No module in the closure
mentions any declaration named in the task's independence list. These
are `SegmentSpecialEssentialSquareIntegrability`,
`SquareIntegrableLanglandsClassification`,
`SegmentEssentialSquareIntegrableClassification`,
`SegmentHeadProductIrreducibility`, `GenericSegmentProductUniqueness`
and `Langlands.Classification.MultisegmentSocleExhaustion`. The closure
also contains no derivative or Zelevinsky material.

The published facts the proof uses are the coinvariant API
`Jacquet.lift`, `Jacquet.mk_apply_subgroup`, `Jacquet.mk_surjective`,
`B.jacquetMk_surjective` and `Representation.Coinvariants.hom_ext`.
It uses the preimage API `radicalInPreimage`, `preimageSection`,
`preimageUnipotentPart`, `preimageProjection` and
`preimageDecomposition`. It uses the representative formulas
`T.normalizedJacquet_mk_eq_inv_halfModulus`,
`T.normalizedRefinedJacquet_mk` and `T.normalizedComposedJacquet_mk`.
It uses the modulus identities `T.leviHalfModulus_refinedUnipotent`,
`T.inverseHalf_composedLeviModulus` and `T.refinedOuterHalfModulus_apply`.
It also uses Mathlib's `NatIso.ofComponents` and the Library's
`SmoothRep.mkIso`. These are definitions and elementary lemmas, not
conclusions of any excluded task.

The proof does not use the excluded tasks or their exact proof
successors and consequences. It does not use a derivative formula,
Zelevinsky 1980 section 9.3 or 9.17, or any classification result. It
also does not import `CoinvariantTowerProof`,
`FlattenedJacquetQuotientProof`, `OppositeRefinementTransitivityProof` or
`RefinementInductionTransitivityProof`. The last two served only as
models for its structure.
