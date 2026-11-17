# Proof: the automorphism group of a pinned split reductive field group

Worker 175.

`Langlands.GroupScheme.pinnedAutomorphismGroup` proves exactly
[`PinnedAutomorphismGroupStatement.{u}`](PinnedAutomorphismGroupStatement.md)
for an arbitrary universe `u`. This is Conrad, *Reductive group schemes* (2014),
Proposition 7.1.6, for a pinned split connected reductive group over a field. Let
`k : Type u` be a field and `G`, `A` group schemes over `Spec k`, with `G` affine. Let
`p : SplitPinning G` be a pinning and `hq : IsAdjointQuotient q` for `q : G ⟶ A`. The
theorem gives group homomorphisms
`inn : A(k) →* Aut G` and `π : Aut G →* p.basedRootDatumAut` such that
`inn x = hq.innerAction.basePointIso x`, `inn` is injective, `π.ker = inn.range`, and
`π (p.basedRootDatumAutLift θ) = θ` for every `θ`. The theorem adds no hypothesis to
the published proposition. The proof uses only published Library results and
Mathlib. It uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

Notation. `A(k)` means `Over.mk (𝟙 (Spec k)) ⟶ A.X`. `inn x` is the automorphism of
`G` by which `x` acts. `L θ` means `p.basedRootDatumAutLift θ`. In
`CategoryTheory.Aut G` the product `σ * τ` is `τ ≪≫ σ`: first `τ`, then `σ`.

## Route

Conrad's proof uses conjugacy of pairs `(T, B)` and the Isomorphism Theorem. The Lean
proof instead uses the following published results.

- Conjugacy of maximal split tori by rational points
  (`smoothMaximalSplitTorusConjugacy`).
- The root-datum automorphism induced by an automorphism that preserves the torus
  (`rootDatumEquivOfTorusCompatibleIso`).
- The projection from root-datum automorphisms to based ones, with a Weyl
  correction (`basedRootDatumProjection`).
- The theorem that a torus-normalizing automorphism acting through the Weyl image is
  inner (`SplitPinning.exists_adjointPoint_of_weylImage`).
- Rationality of normalizing points for split maximal tori
  (`splitMaximalTorusWeylRationality`).

It does not use Conrad's Proposition 6.2.11(2). The proof has four steps:

1. The action of `A(k)` is an injective homomorphism `inn`.
2. The range of `inn` is normal.
3. Every automorphism is `inn x * L θ` (existence).
4. `inn x = L θ` forces `θ = 1` (uniqueness).

Then `π σ` is defined as the unique `θ` with `σ * (L θ)⁻¹ ∈ inn.range`.

## Step 1: the homomorphism `inn` (`innerHom`, `innerHom_injective`)

`comp_eq_constantPoint` (Lean line 33) says that a base point restricted along any
`t : W ⟶ Spec k` is the constant point `H.constantPoint x W`. `innerHom` (line 43)
sends `x` to `hq.innerAction.basePointIso x`. It respects `1` and products: check on
`W`-points with `AutomorphicAction.comp_basePointIso_hom`, then use
`constantPoint_one`, `constantPoint_mul`, and the action laws `act_one_left` and
`act_mul_left`. `innerHom_apply` (line 64) holds by `rfl`. So the first conclusion of
the statement is definitional.

Injectivity (`innerHom_injective`, line 68) follows from faithfulness of the action,
`IsAdjointQuotient.innerAction_isFaithful` in
[`Rational.InnerDiscrepancy`](../Rational/InnerDiscrepancy.md). Suppose
`inn x = inn y`. Then for every test object `W`, every `t : W ⟶ Spec k` and every
point `g` of `G`, `g` is acted on in the same way by `t ≫ x` and by `t ≫ y`. By
`comp_eq_constantPoint`, these are the constant points of `x` and `y`.

## Step 2: normality (`conj_innerHom`, `conj_mem_range`)

`comp_mem_center` (line 80) shows that an automorphism `σ` maps central points of `G`
to central points. Indeed, `y = (y ≫ σ⁻¹) ≫ σ` and composition with `σ` is
multiplicative. So `σ.hom ≫ q` kills the centre (`killsCenter_comp`, line 95). By the
universal property of `hq` it factors as `q ≫ σ_A`, with
`σ_A := hq.desc (σ.hom ≫ q) _` (`IsAdjointQuotient.comp_desc`).

`conj_innerHom` (line 102) proves
`inn (x ≫ σ_A) = σ * inn x * σ⁻¹`. The proof compares the two maps on `W`-points
`g`. By `AutomorphicAction.hom_ext_of_local_quotient_lift`
([`ActionDescent`](../ActionDescent.md)), it suffices to check after restricting to
any `b : V ⟶ W` along which the constant point `x_W` lifts to a point `h` of `G`,
that is, `b ≫ x_W = h ≫ q`. Then `b ≫ x_W ≫ σ_A = (h ≫ σ) ≫ q`. On both sides
`IsAdjointQuotient.innerAction_act_lift`
([`Adjoint.InnerAction`](../Adjoint/InnerAction.md)) turns the action of a lifted
point into conjugation. Writing `σ(-)` for composition with `σ.hom` and `g` for the
restricted point, the left side gives `σ(h) · g · σ(h)⁻¹`, and the right side gives
`σ(h · σ⁻¹(g) · h⁻¹)`. These agree because `σ` is a homomorphism
(`MonObj.mul_comp`, `GrpObj.inv_comp`) and `σ⁻¹ ≫ σ = 𝟙`. `conj_mem_range` (line 133) records the consequence
`σ * inn x * σ⁻¹ ∈ inn.range`.

## Step 3: existence (`exists_eq_innerHom_mul_lift_of_normalizes`, `exists_eq_innerHom_mul_lift`)

**Torus-normalizing automorphisms** (line 214). Let `f : Aut G` and
`t : p.torus ≅ p.torus` with
`p.inclusion ≫ f.hom = groupHom t.hom ≫ p.inclusion`.

- Let `δ := rootDatumEquivOfTorusCompatibleIso … f t …`
  ([`Reductive.GeometricRootDatumComparison`](GeometricRootDatumComparison.md)). This
  is an automorphism of `p.rootDatum` with `δ.weightMap χ = t.hom ≫ χ`.
- Let `θ := p.basedRootDatumProjection δ⁻¹`
  ([`Reductive.BasedRootDatumProjection`](BasedRootDatumProjection.md)). By
  `basedRootDatumProjection_correction`, `θ * δ` lies in the Weyl group `W`.
- Let `tθ := p.basedRootDatumAutTorusLift θ`
  ([`Reductive.PinnedAutomorphismLift`](PinnedAutomorphismLift.md)). Then
  `θ.weightMap χ = tθ.inv ≫ χ` (`basedRootDatumAutTorusLift_character`).
- The square `basedRootDatumAutLift_square` gives
  `p.inclusion ≫ (L θ).inv = groupHom tθ.inv ≫ p.inclusion`.
- So `f * (L θ)⁻¹` normalizes the torus through `tθ.symm ≪≫ t`.
- Its character automorphism `characterAut (tθ.symm ≪≫ t)` (the map `χ ↦ t.inv ≫ tθ.hom ≫ χ`) is the
  image under `weightHom` of `(θ * δ)⁻¹ ∈ W`. This is checked on characters with
  the formulas above.
- `IsRootDatumOf.abstractWeylImage_le`
  ([`Reductive.RootDatumWeylComparison`](RootDatumWeylComparison.md)) places it in the
  actual Weyl image `weylImage p.inclusion`.
- `SplitPinning.exists_adjointPoint_of_weylImage`
  ([`Reductive.PinnedWeylInner`](PinnedWeylInner.md)) gives `x ∈ A(k)` with
  `inn x = f * (L θ)⁻¹`, that is, `f = inn x * L θ`.

**Arbitrary automorphisms** (line 265). Let `σ : Aut G`.

- Both `p.inclusion ≫ σ.hom` and `p.inclusion` are maximal split tori:
  `IsMaximalTorus.comp_iso` ([`Torus.MaximalTransport`](../Torus/MaximalTransport.md))
  and `IsMaximalTorus.isMaximalSplitTorus`
  ([`Torus.MaximalSplitComparison`](../Torus/MaximalSplitComparison.md)).
- `smoothMaximalSplitTorusConjugacy`
  ([`Rational.SmoothMaximalSplitTorusConjugacyProof`](../Rational/SmoothMaximalSplitTorusConjugacyProof.md))
  applies, because `G` is smooth, affine and connected. It gives `g ∈ G(k)` and an
  isomorphism `e` of tori with
  `p.inclusion ≫ σ.hom ≫ (G.innerIso g).hom = e.hom ≫ p.inclusion`.
- So `a * σ` normalizes the pinned torus, where `a := G.innerIso g`. By the previous
  paragraph, `a * σ = inn x * L θ`.
- `SplitPinning.innerAction_basePointIso_lift` gives `inn (g ≫ q) = a`.
- Hence `σ = inn ((g ≫ q)⁻¹ * x) * L θ`.

## Step 4: uniqueness (`exists_isNormalizingPoint`, `eq_one_of_innerHom_eq_lift`)

**Lemma** (`exists_isNormalizingPoint`, line 146). Let `z ∈ A(k)` and suppose `inn z`
normalizes the pinned torus through `t`. Then some `n ∈ G(k)` satisfies
`IsNormalizingPoint p.inclusion n t`. The proof passes to `K = AlgebraicClosure k`
along `b := algebraBaseMap k K`.

- The base change `q_K` of `q` is surjective and locally of finite type, because
  `DominantHomFlat.baseChange_isPullback` exhibits it as a pullback of `q`.
- `exists_rationalPointLift`
  ([`Absolute.QuotientNormalizer`](../Absolute/QuotientNormalizer.md)) lifts the
  base-changed point `z_K` to `h ∈ G_K(K)`.
- The key identity is that the base change of `inn z` equals `G_K.innerIso h`. It is
  proved on points through `baseChangePointsEquiv`. Its compatibilities
  `baseChangePointsEquiv_comp` and `baseChangePointsEquiv_constantPoint` reduce it to
  `innerAction_act_lift` for the lift `h` of `z`.
- So `h` normalizes the base-changed torus through the base change of `t`.
- `splitMaximalTorusWeylRationality`
  ([`Reductive.SplitWeylRationality`](SplitWeylRationality.md)) gives `n ∈ G(k)` and
  an automorphism `σ'` of `p.torus`. The point `n` normalizes through `σ'`, and `σ'`
  base-changes to the base change of `t`.
- Base change along `Spec K → Spec k` is faithful
  (`GaloisCocharacterDescent.faithful_algebraPullback`,
  [`Absolute.CocharacterDescentGroup`](../Absolute/CocharacterDescentGroup.md)).
  Hence `σ' = t`.

**Uniqueness** (`eq_one_of_innerHom_eq_lift`, line 195). Suppose `inn x = L θ`.

- `L θ` normalizes the torus through `tθ` (`basedRootDatumAutLift_square`).
- By the lemma, some `n ∈ G(k)` normalizes the torus through `tθ`.
- `StarActionIndependence.exists_weyl_of_isNormalizingPoint`
  ([`Reductive.StarActionIndependenceProof`](StarActionIndependenceProof.md)) gives
  `w ∈ W` with `w.weightMap χ = tθ.inv ≫ χ = θ.weightMap χ`.
- `StarActionIndependence.equiv_ext_of_weightMap` gives `θ = w`.
- So `θ` is both a Weyl element and based. `eq_one_of_weyl_of_based` gives `θ = 1`.

## Assembly (`pinnedAutomorphismGroup`, line 291)

Two facts follow from the steps:

- (E) For every `σ` there is `θ` with `σ * (L θ)⁻¹ ∈ inn.range`. This is Step 3.
- (U) If `σ * (L θ)⁻¹` and `σ * (L θ')⁻¹` both lie in `inn.range`, then `θ = θ'`. Write
  them as `inn x` and `inn y`. Then `inn (y⁻¹ * x) = L (θ' * θ⁻¹)`, so `θ' * θ⁻¹ = 1`
  by Step 4.

Let `π₀ σ` be a chosen `θ` from (E).

- **`π₀` is multiplicative.** We have
  `σ τ (L(π₀ σ · π₀ τ))⁻¹ = (σ (τ (L(π₀ τ))⁻¹) σ⁻¹) · (σ (L(π₀ σ))⁻¹)`. The first
  factor is in `inn.range` by Step 2 and the second by (E). So (U) gives
  `π₀ (σ τ) = π₀ σ · π₀ τ`. Then `π := MonoidHom.mk' π₀ _`.
- **`inn` is injective.** This is Step 1.
- **`π.ker = inn.range`.** Let `σ` be in the kernel. Then `π₀ σ = 1`, so
  `σ = σ * (L 1)⁻¹ ∈ inn.range`. Conversely, let `σ ∈ inn.range`. Then (U), applied
  to `1` and `π₀ σ`, gives `π₀ σ = 1`.
- **`π ∘ L = id`.** `L θ * (L θ)⁻¹ = 1 ∈ inn.range`, so (U) gives `π₀ (L θ) = θ`.
