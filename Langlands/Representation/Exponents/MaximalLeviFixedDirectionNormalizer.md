# Conjugations fixing a missed direction lie in the parabolic

Author: Worker 1714. This module is an internal conditional reduction for the proof of
Renard VII.1.3.

## Statements

`MaximalLeviFixedDirectionNormalizerStatement` says the following, over every field `k`.

- Let `G` be connected reductive, and let `p : P ⟶ G` be an actual maximal proper rational
  parabolic with rational Levi `l : M ⟶ P` and split component `a : A ⟶ M`. Maximality has
  the form used in the published `MaximalLeviContainmentStatement` and
  `MaximalLeviConeComplementStatement`.
- Let `q : Q ⟶ G` be a rational parabolic with a Levi factor `lQ : M ⟶ Q` such that
  `lQ ≫ q = l ≫ p`. Let `rQ` be a geometric unipotent radical of `Q`, and let `Q` have a
  root presentation for `a`.
- Let `w ∈ G(k)`, `σ : M ≅ M` and `e : A ≅ A` satisfy
  `σ ≫ l ≫ p = l ≫ p ≫ Int(w)` and `e ≫ a = a ≫ σ`.
  So `w` normalizes the image of `M`, and `e` is the induced automorphism of `A`.
- Let `y ∈ X^*(A) ⊗ ℝ` be nonzero, and let its pairing with every cocharacter `ν` of `A`
  whose image is central in `G` vanish.

If `e` fixes `y`, that is `y ∘ e = y`, then `w ∈ Q(k)` (`w ∈ pointImage q`).

`MaximalLeviFixedDirectionNormalizerReductionStatement` is the implication

```lean
MaximalLeviConeComplementStatement.{u} →
  ParabolicSelfNormalizerStatement.{u} →
    MaximalLeviFixedDirectionNormalizerStatement.{u}
```

`maximalLeviFixedDirectionNormalizer_of_coneComplement` proves it. Neither premise is
proved here; both are published statements, used unchanged.

## Provenance

The reduction is internal, with no separate counterpart in the literature. It is the
group-theoretic half of a uniqueness claim in Renard's proof of VII.1.3: the exponent `ω`
of `ρ` occurs in only one piece of the geometric lemma for a parabolic with Levi `M`.
Renard uses this implicitly when he concludes that `ω` is an exponent of exactly one of
`π₁, π₂` along `P`.

## Source

Renard, VII.1.3, proof (printed pp.224–226, PDF pp.230–232). Renard writes `w.P` for the
parabolic opposite to `P'` with Levi `w.M` (PDF p.230). He also uses
"Comme M est maximal, A_M/A_G est de dimension 1" (PDF p.231).

## The proof

The lemmas live in namespace `Langlands.GroupScheme`.

1. `ParabolicRootPresentation.notMem_positiveCone_or_neg_notMem`: the positive cone of a
   presentation is pointed, so for `y ≠ 0`, `y` or `-y` lies outside it. With no
   restricted roots the cone is `{0}` (`positiveCone_of_eq_empty`). Otherwise the
   evaluation at the presentation's defining cocharacter is positive on the cone
   (`splitComponentEvaluation_pos_of_mem_positiveCone`). It cannot be positive at both
   `y` and `-y`.
2. `mem_pointImage_of_fixes_of_notMem_positiveCone` handles a direction `y` outside the
   cone of the given presentation `pres` of `Q`.
   1. `pres₂ := pres.conjugate w σ e ha he` (from module
      `Langlands.Representation.Exponents.MaximalLeviExponentTransport`): `pres` transported
      along `Int(w)`, with Levi reparametrized by `σ⁻¹` and split component by `e⁻¹`. It is a
      presentation of `q ≫ Int(w)`, which is `wQw⁻¹`, with Levi factor `σ⁻¹ ≫ lQ` and split
      component `a`. The new Levi has the composite `l ≫ p` into `G`, by the hypothesis on `σ`.
   2. By `positiveCone_conjugate` (same module), the cone of `pres₂` is the image of the cone
      of `pres` under restriction along `e⁻¹`.
   3. Since `e` fixes `y` (with `rationalCharacterRestrictReal_comp_apply` and
      `rationalCharacterRestrictReal_id_apply` from the same module), `y` is not in the cone
      of `pres₂`.
   4. `MaximalLeviConeComplementStatement`, applied to `Q` and `wQw⁻¹`, gives
      `range q = range (q ≫ Int(w))`.
   5. `mem_pointImage_of_range_comp_innerIso_eq` turns this into membership. Both
      monomorphisms represent the same subgroup functor, so `isoOfIsRepresentedBy`
      gives an isomorphism of `Q` with itself compatible with `Int(w)`. By
      `mem_normalizer_range_of_innerIso`, `w` normalizes `range q`.
      `ParabolicSelfNormalizerStatement` gives `w ∈ range q`, that is `w ∈ Q(k)`.
3. `mem_pointImage_of_fixes` combines 1 and 2. If `-y` is the direction outside the
   cone, the central-vanishing and fixed-point hypotheses pass to `-y` by linearity.
4. `maximalLeviFixedDirectionNormalizer_of_coneComplement` applies
   `mem_pointImage_of_fixes` to the bound data of the statement.

## Scope

The field is arbitrary. The statement uses universe `u` for the field, as both premises
do. No local-field structure and no representation theory enters.
