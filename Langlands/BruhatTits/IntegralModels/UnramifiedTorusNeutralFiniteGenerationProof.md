# Proof: torus points modulo neutral integral points are finitely generated

Module `Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationProof`.

The theorem
`Langlands.BruhatTits.IntegralModels.unramifiedTorusNeutralFiniteGeneration`
has exactly the type
`UnramifiedTorusNeutralFiniteGenerationStatement.{u}`, at arbitrary universe
`u`. The statement pair is unchanged.

## Statement proved

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F`,
`O = fixedFieldIntegers F`, and `T` a torus over `Spec K`. Let
`D : RelativeComponentModelData O K T` be model data whose full
integral-point image is `characterValuationKernel (fixedFieldValuation F) T`.
Then some finite set `s` of rational points of `T` satisfies
`Subgroup.closure s ⊔ D.neutral.integralPoints = ⊤`.

## Proof

Write `T(K)` for `rationalPoints T`, `B = D.full.integralPoints` and
`N = D.neutral.integralPoints`.

1. **`T(K)` modulo `B` is finitely generated.** Let
   `v = MaximalUnramified.valuation F`, the Library's normalized
   `ℤ`-valued valuation on `K`. Let
   `Φ = IntegerValuation.rationalCharacterValuation v T`, the homomorphism
   `T(K) → Multiplicative (X →+ ℤ)` with `X = rationalCharacters T` that sends
   `g` to `χ ↦ -log v(χ(g))`. By `IntegerValuation.rationalCharacterValuation_ker`,
   the kernel of `Φ` is `characterValuationKernel v T`.
   `characterValuationKernel_maximalUnramified` shows that this equals
   `characterValuationKernel (fixedFieldValuation F) T`: the two valuations
   are equivalent (`MaximalUnramified.valuation_isEquiv`), so they have the
   same elements of value one. By hypothesis this kernel is `B`.

   `characterDual_finite`: a torus is connected reductive
   (`IsTorus.isConnectedReductive_of_fieldSplitting`), so `X` is a finite free
   `ℤ`-module (`rationalCharacterLattice`). Therefore `X →+ ℤ`, which is
   `ℤ`-linearly equivalent to `X →ₗ[ℤ] ℤ` (`addMonoidHomLequivInt`), is a
   finite `ℤ`-module (`Module.Finite.linearMap`).

   `exists_finite_closure_sup_ker` is a general group-theoretic lemma: if
   `Φ : G →* Multiplicative A` with `A` a finite `ℤ`-module, then some finite
   `s₁ ⊆ G` has `closure s₁ ⊔ ker Φ = ⊤`. The image of `Φ`, viewed as a
   `ℤ`-submodule of `A`, is finitely generated because `A` is Noetherian. Pick
   preimages of a finite spanning set. Span induction shows that the closure
   of these preimages maps onto the image of `Φ`, and
   `Subgroup.map_eq_range_iff` turns this into `closure s₁ ⊔ ker Φ = ⊤`.
   Here this gives `closure s₁ ⊔ B = ⊤`.

2. **`N` has finite index in `B`, in the form used.** The ring `O` is a
   local domain (a valuation subring), and the full model is smooth. So the
   instance `RelativeComponentModelData.neutralSections_finiteIndex` from
   `RelativeComponentFiniteIndex` shows that `D.neutralSections` has finite
   index in `D.full.integralSections`.

   `exists_finite_closure_sup_eq_top`: a finite-index subgroup `H`, together
   with the finite set of chosen coset representatives (`Quotient.out`),
   generates the group (`QuotientGroup.mk_out_eq_mul`).

   `exists_finite_range_le_closure_sup_map`: for `f : G' →* G`, take the image
   of these representatives under `f`. Then `f.range ≤ closure s₂ ⊔ H.map f`
   by `Subgroup.map_sup` and `MonoidHom.map_closure`.

   Apply this to `f = D.full.integralPointMap` (range `B`) and
   `H = D.neutralSections`. Here `H.map f = D.neutralPoints`, which is `N` by
   `RelativeComponentModelData.neutralPoints_eq`. So
   `B ≤ closure s₂ ⊔ N`.

3. **Conclusion.** Take `s = s₁ ∪ s₂`, which is finite. Then
   `closure s ⊔ N = closure s₁ ⊔ (closure s₂ ⊔ N) ≥ closure s₁ ⊔ B = ⊤`, using
   `Subgroup.closure_union` and associativity of `⊔`.

## Helper module

`Langlands/BruhatTits/IntegralModels/RelativeComponentFiniteIndex.lean`
(with its Markdown) proves step 2's finite-index instance. That proof
reduces to the closed fibre and uses the Library's finite rational component
group over a field. It needs no Hensel lifting.

## Relation to the source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), proof of
Corollary B.8.6 (printed p. 683 / PDF p. 714), argues that `B^ft(Ô)/B^0(Ô)` is
finite and that `B(K)/B(K)^1` embeds in a finitely generated group (Lemma
11.1.3, printed p. 422 / PDF p. 453). The Lean proof follows the same two
steps. For the first, it maps into the full dual `Hom(X^*(T), ℤ)` of the
`K`-rational characters, rather than `X_*(T)_I`. Finite generation of any
subgroup of a finitely generated abelian group suffices, so injectivity
modulo the kernel is all that is used. For the second, finiteness comes from
the closed fibre's component group, as described in the helper module.
