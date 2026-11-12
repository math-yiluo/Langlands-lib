# Second adjointness is equivalent to the contragredient formula

Author: Worker 1222. Module
`Langlands.Representation.Exponents.LeviSecondAdjointnessContragredientEquivalenceStatement`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement
`LeviSecondAdjointnessContragredientEquivalenceStatement : Prop`; nothing is proved here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VI.9.6, printed pp.201–202 / PDF pp.207–208. The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Let `P = MN` be a parabolic subgroup of `G` and `P̄ = M N̄` the opposite parabolic. VI.9.6
states two Theorems:

- (VI.9.6.1), second adjointness: `r_{P̄}^G` is right adjoint to `i_P^G`, that is
  `Hom_G(i_P^G τ, π) ≃ Hom_M(τ, r_{P̄}^G π)` naturally;
- (VI.9.6.2): `r_{P̄}^G π̃ = (r_P^G π)~` for every smooth `π` of `G`.

Between them the source says, in translation: "We will see that it follows from the Jacquet
lemma. Let us first show that it is equivalent to the following statement", and then gives
a proof of the equivalence (the "Démonstration" on printed pp.201–202 / PDF pp.207–208).
That proof ends with the existence of a natural isomorphism
`r_{P̄}^G π̃ ≃ (r_P^G π)~`, obtained from A.III.3. This module states that equivalence. The
two Theorems themselves are the published statements `LeviSecondAdjointnessStatement` and
`LeviJacquetContragredientStatement` (same namespace, modules
`Langlands.Representation.Exponents.LeviSecondAdjointnessStatement` and
`Langlands.Representation.Exponents.LeviJacquetContragredientStatement`). Those statements
quantify over all fields and groups, so their equivalence as propositions says nothing about
a fixed pair of parabolics. The source's equivalence holds for each fixed `G`, `P` and `P̄`,
and the present statement is pointwise in the same way.

## Statement

The binders and hypotheses are exactly those of `LeviSecondAdjointnessStatement` and
`LeviJacquetContragredientStatement`. The statement quantifies over a field `k : Type u` with
`[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`
and a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs
`hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on
`rationalPoints G` and assumes `[LocallyCompactSpace (rationalPoints G)]` and
`[NonarchimedeanGroup (rationalPoints G)]`. It quantifies over two actual rational parabolic
triples with the same Levi group scheme `M`:

- `P = MN`: `p : P ⟶ G`, `m : M ⟶ P`, `n : N ⟶ P` with `hp`, `hm`, `hn`, `hmul`;
- `P̄ = M N̄`: `pbar : Pbar ⟶ G`, `mbar : M ⟶ Pbar`, `nbar : Nbar ⟶ Pbar` with `hpbar`,
  `hmbar`, `hnbar`, `hmulbar`.

It assumes `mbar ≫ pbar = m ≫ p` and `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`:
the two triples have the same Levi embedding and `P(F) ∩ P̄(F) = M(F)`. The Markdown of
`LeviSecondAdjointnessStatement` explains why these hypotheses describe the opposite
parabolic. On `rationalPoints M` it installs `hm.isConnectedReductive.isAffineHom`, the
canonical topology `leviPointTopology m hm`, and the instances
`leviPoints_locallyCompactSpace p m hp hm` and `leviPoints_nonarchimedeanGroup p m hp hm`.
It then asserts

```
Nonempty (leviInductionFunctor.{u, max u v} p m n … ⊣
    leviJacquetFunctor.{u, max u v} pbar mbar nbar …) ↔
  Nonempty (SmoothRep.contragredientFunctor.{0, u, max u v} ⋙
      leviJacquetFunctor.{u, max u v} pbar mbar nbar … ≅
    (leviJacquetFunctor.{u, max u v} p m n …).op ⋙
      SmoothRep.contragredientFunctor.{0, u, max u v})
```

The left side is the conclusion of `LeviSecondAdjointnessStatement` for this pair of
parabolics. The right side is the conclusion of `LeviJacquetContragredientStatement` for this
pair, at the carrier universe `max u v`.

## The objects

- `leviInductionFunctor p m n …` is the published normalized parabolic induction `i_P^G`;
  `leviJacquetFunctor p m n …` and `leviJacquetFunctor pbar mbar nbar …` are the published
  normalized Jacquet functors `r_P^G` and `r_{P̄}^G`. Their normalizations are described in
  the Markdown of `LeviSecondAdjointnessStatement` and `LeviJacquetContragredientStatement`.
- `SmoothRep.contragredientFunctor` is the published contravariant smooth contragredient
  `π ↦ π̃`. With coefficients `ℂ` in `Type`, it preserves the carrier universe.
- `F ⊣ G'` is Mathlib's `Adjunction`, which is (VI.9.6.1) with naturality in both variables.
  The isomorphism on the right is an isomorphism of functors
  `(SmoothRep ℂ G(F))ᵒᵖ ⥤ SmoothRep ℂ M(F)`, which is (VI.9.6.2) read as a natural
  isomorphism in `π`, as the source's proof concludes.

## Universes

`leviInductionFunctor.{u, w}` sends carriers in `Type w` to carriers in `Type (max u w)`, and
Mathlib's `Adjunction` needs both functors between the same two categories. As in
`LeviSecondAdjointnessStatement`, both sides are taken at the carrier universe `max u v` for
an arbitrary `v`; then `max u (max u v) = max u v`. `LeviJacquetContragredientStatement` is
published for an arbitrary carrier universe; here it is used at `max u v`, so that the two
sides of the equivalence concern the same categories of representations.

## Faithfulness notes

- The equivalence is asserted for each fixed pair `P`, `P̄`, as in the source, and not
  between the two universally quantified Theorems.
- No admissibility or finiteness is assumed for any representation, as in the source.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses. Those of
  `M(F)` are derived from them, not assumed.
- Both directions are asserted. The source proves both: (VI.9.6.2) ⇒ (VI.9.6.1) through the
  chain (VI.9.6.3) and left exactness, and (VI.9.6.1) ⇒ (VI.9.6.2) through the chain and
  A.III.3.

## Remaining obligations

The proof is a separate obligation. The source's argument uses Lemma I.4.2.1
(`Hom_G(π, σ̃) ≃ Hom_G(σ, π̃)`), the fact that normalized induction commutes with
contragredients (the source does not cite it at this point; it is (IV.2.1.2)), the first
adjunction `r_P^G ⊣ i_P^G` (VI.1.2), left exactness of
`Hom_G(X, ·)` and of `r_{P̄}^G` applied to `0 → π → π̃̃ → π̃̃_1`, and A.III.3 (Yoneda) for
the converse. The Library already contains abstract pieces of the direction
(VI.9.6.2) ⇒ (VI.9.6.1): `Langlands.SmoothRep.nonempty_adjunction_of_frobeniusChain_unit`
(module `Langlands.Representation.Category.ChainUnitAdjunction`) builds `L ⊣ R` from the
chain under an additional per-object condition on the unit, which its Markdown records as
not stated by the source. None of this is asserted here.

## Provenance

This is a derived statement of the equivalence proved in VI.9.6 between its two Theorems,
for the represented-parabolic interface. Its two sides are, verbatim, the conclusions of the
published `LeviSecondAdjointnessStatement` and `LeviJacquetContragredientStatement` for one
pair of parabolics, at the common carrier universe `max u v`.
