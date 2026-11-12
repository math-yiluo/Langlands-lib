# Levi subgroups of proper parabolics containing a maximal Levi: proof

Author: Worker 4967 (Task 4967). The proof combines two published Library theorems;
their authors are named in their own Markdown files
([`MaximalLeviDynamicReduction`](MaximalLeviDynamicReduction.md) and
[`Absolute.ParabolicDynamicProof`](../Absolute/ParabolicDynamicProof.md)).

`Langlands.GroupScheme.maximalLeviContainment.{u}` proves exactly the unchanged
published proposition `Langlands.GroupScheme.MaximalLeviContainmentStatement.{u}`
(module `Langlands.GroupScheme.Rational.MaximalLeviContainmentStatement`). It has no
hypotheses. The field `k : Type u` is arbitrary, with no assumption on its
characteristic and no perfectness assumption. `G` is a connected reductive group over
`Spec k`. Let `p : P ⟶ G` be a parabolic subgroup with rational Levi `l : M ⟶ P`, such
that `p` is not an isomorphism and is maximal in the statement's sense. Let
`q : Q ⟶ G` be a parabolic subgroup with rational Levi `lQ : L ⟶ Q`, such that `q` is
not an isomorphism. If `SubgroupFunctor.range (l ≫ p) ≤ SubgroupFunctor.range (lQ ≫ q)`,
the theorem gives `SubgroupFunctor.range (l ≫ p) = SubgroupFunctor.range (lQ ≫ q)`.
This is an equality of subgroup functors of `G`, so it holds on every test scheme.

## Implemented proof

The proof is a single term:

```lean
theorem maximalLeviContainment : MaximalLeviContainmentStatement.{u} :=
  maximalLeviContainment_of_parabolicDynamic parabolicDynamic
```

It uses two published theorems.

1. `Langlands.GroupScheme.maximalLeviContainment_of_parabolicDynamic`, in module
   `Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction`, proves
   `MaximalLeviContainmentFromParabolicDynamic.{u}`. By definition this is the
   implication `ParabolicDynamicStatement.{u} → MaximalLeviContainmentStatement.{u}`.
   The implication has no other premise.
2. `Langlands.GroupScheme.parabolicDynamic`, in module
   `Langlands.GroupScheme.Absolute.ParabolicDynamicProof`, proves
   `ParabolicDynamicStatement.{u}` (Milne, Theorem 25.1) with no hypotheses. For a
   connected reductive `G` over any field and a closed subgroup `i : P ⟶ G`, it says
   that `i` is parabolic exactly when `SubgroupFunctor.range i = Dynamic.parabolic χ`
   for some cocharacter `χ : Gm ⟶ G` defined over the ground field.

Applying the first theorem to the second gives the target at the same universe `u`.

## The argument inside the reduction

The Lean proof above only applies the published reduction. That reduction argues as
follows; the complete account is in its own Markdown.

1. *Dynamic presentations.* By `parabolicDynamic`, `P = P(χ)` and `Q = P(τ)` for
   cocharacters `χ, τ` of `G` over `k`.
2. *A common split component.* `exists_commonSplitComponentCocharacters_of_levi_le`
   takes a split component `a : A ⟶ M` of `M`, from the published
   `splitComponentStatement`. It produces `ζ, η ∈ X_*(A)` such that `p` represents
   `P(ζ)` with `Z(ζ) = M`, and `q` represents `P(η)` with `Z(η) = L` (cocharacters
   viewed in `G` through `a ≫ l ≫ p`). The cocharacter for `Q` first comes from
   `IsRationalLeviSubgroup.exists_centralCocharacter_of_dynamicParabolic`; it is
   central in `L`. Since `M ⊆ L` it commutes with `M`, so it lies in `Z(ζ) = M` and is
   central there. `IsSplitComponent.exists_factor` then factors it through `A`.
3. *`L` is proper.* If `Z(η)` were all of `G`, then `P(η)` would be all of `G`. Then
   `q` would be a monomorphism with full range, hence an isomorphism
   (`isIso_of_full_range`), contrary to the hypothesis on `q`.
4. *Strictness gives a coarsening.* Suppose `M ≠ L`. Then `Z(ζ) < Z(η)`. The finite-weight
   lemma `exists_properCentralizerCoarsening` (module `MaximalLeviFiniteWeights`)
   gives `μ ∈ X_*(A)` with three properties: `P(ζ) ≤ P(μ)`, `Z(ζ) < Z(μ)` and
   `Z(μ) ≠ G`.
5. *Maximality.* The affine representative `q' : P(μ) ⟶ G` is a parabolic subgroup by the
   reverse direction of `parabolicDynamic`, and `p` factors as `j ≫ q'`. By maximality of
   `P`, either `j` or `q'` is an isomorphism.
   - If `j` is an isomorphism, then `p` represents `P(μ)`.
     `IsRationalLeviSubgroup.centralizer_eq_of_dynamicParabolic` then gives
     `Z(μ) = M = Z(ζ)`. This contradicts `Z(ζ) < Z(μ)`.
   - If `q'` is an isomorphism, then `P(μ)` is all of `G`.
     `Dynamic.parabolic_eq_top_iff_centralizer_eq_top` applies because `G` has trivial
     unipotent radical. It gives `Z(μ) = G`, which contradicts `Z(μ) ≠ G`.

So `M = L` as subgroup functors of `G`.

## Relation to the source argument

The statement's Markdown sketches Renard's argument (VII.1.3, PDF p.230–231): `A_L ⊆ A_M`,
`dim A_M / A_G = 1`, and `L = Z_G(A_L)`. The implemented proof takes a different route.
It does not use the dimension of `A_M / A_G`, any relative root system, standard
parabolics or Levi conjugacy. The maximality hypothesis is used directly on the
intermediate parabolic `P(μ)` built in step 4.

## Scope and checks

Nothing is restricted: every field `k : Type u`, every connected reductive `G`, and the
exact binders and hypotheses of the published statement. The statement's Lean/Markdown
pair and the pairs it imports are unchanged. A development `lean_check` in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` compiled the module with no errors or warnings.
It reported only the axioms `propext`, `Classical.choice` and `Quot.sound`.
