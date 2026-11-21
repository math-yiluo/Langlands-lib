# Galois coverings at the level of germs

Worker 749. This module is a derived categorical helper for the planned proof of
`AnalyticEtaleGaloisCoinducedLocalAcyclicStatement`. It passes from single Galois coverings
to germs along a cofiltered system of objects. It then assembles the result into a
Galois–Čech system, leaving local lifting as the only hypothesis.

The module imports the following:

- `Langlands.Cohomology.GaloisCartan`, for `NaturalAction` and `GaloisCechSystem`;
- `Langlands.Cohomology.GaloisCoveringCech`, for `GaloisCovering`, Galois descent and
  injective acyclicity at one covering;
- `Langlands.Cohomology.CoinducedFilteredAcyclic`, for group cohomology of filtered colimits;
- Mathlib's AB5 property of module categories.

## Background and provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), Proposition 4.2.4
and its proof (printed pp. 87–88, source `berkovich-1993-etale-cohomology`), computes Čech
complexes of finite germ coverings as filtered colimits of Čech complexes over neighbourhoods.
This module formalizes the categorical part of that passage. It does not formalize the
proposition itself.

Two facts are used:

- filtered colimits of modules are exact (Mathlib's `AB5 (ModuleCat R)`);
- for a finite group, cohomology commutes with filtered colimits of representations
  (`CoinducedFilteredAcyclic.isZero_groupCohomology_of_isColimit`, from Serre, *Galois
  Cohomology* I §2.2 Proposition 8, printed p. 11, source `serre-1997-galois-cohomology`).

The constructions and proofs are internal.

## Setting

`C` is a category with a Grothendieck topology `J`, and `R` is a commutative ring in `Type w`.
`I : Type w` is a small cofiltered category. Germs are colimits over `Iᵒᵖ`. Some results also
assume that `C` is locally `w`-small and that module sheafification exists.

## Germ functors

- `germ J R V`, for `V : I ⥤ C`, is the functor sending a module sheaf `F` to
  `colimit (V.op ⋙ F.obj)`. `germι J R V F i` is the germ map from `F(V i)`.
- `germMap J R α : germ J R V ⟶ germ J R V'`, for `α : V' ⟶ V`, is restriction of germs.
  `germι_germMap` computes it on germs of sections. It is functorial:
  `germMap_id`, and `germMap_comp` (`germMap (β ≫ α) = germMap α ≫ germMap β`).
- Every germ functor is additive and preserves finite limits (instances). This uses AB5
  for `ModuleCat`, since `sheafToPresheaf` and precomposition preserve limits.
- `germι_eq_germι_map` (germs are invariant under restriction along the system) and
  `map_comp_eq_of_map_eq` (equal restrictions stay equal after further restriction) are
  helper lemmas.

## Germ Galois data

`GermGaloisDatum J Γ V' V`, for a group `Γ : Type w` and `V' V : I ⥤ C`, consists of the
following.

- A natural transformation `p : V' ⟶ V`.
- Natural deck transformations `deck : Γ → (V' ⟶ V')` with `deck 1 = 𝟙`,
  `deck (γ * δ) = deck δ ≫ deck γ` and `deck γ ≫ p = p`.
- At every index `i`, the conditions `covering`, `locally_transitive` and `locally_free`
  of `GaloisCovering` for the components `p.app i` and `(deck γ).app i`.

`coveringAt D i` is the resulting `GaloisCovering J Γ (V'.obj i) (V.obj i)`.

- `action D R` is the natural action of `Γ` on `germ J R V'` (a `NaturalAction`): `γ` acts
  by `germMap (deck γ⁻¹)`. `germι_act_apply` computes it on germs.
- `aug D R := germMap J R D.p`. `germι_aug_apply` computes it on germs.
- `aug_act`: the augmentation lands in the invariants, since `deck γ⁻¹ ≫ p = p`.
- `aug_injective`: the augmentation is injective. Proof: if the germ of `F(p_i) s` is zero,
  the section vanishes after restriction to some stage `k`. By naturality of `p`, that
  restriction is `F(p_k)` of the restriction of `s`. Injectivity of restriction along
  `p_k` (`GaloisCovering.map_p_injective`) shows that the germ of `s` is zero.
- `exists_aug_eq`: for finite `Γ`, every invariant germ along `V'` is in the image of the
  augmentation. Represent the germ by `t` over some stage. For each `γ`, invariance holds
  after restriction to a later stage, and coequalizers in the filtered category `Iᵒᵖ`
  make the two restriction arrows agree. Induction over `Finset.univ`, using maxima and
  coequalizers, gives a single stage `k` on which the restriction of `t` is invariant
  under every deck transformation. Galois descent at `k` (`GaloisCovering.exists_map_p_eq`)
  gives a section over `V k`. Its germ maps to the germ of `t`.
- `repDiagram D R F : Iᵒᵖ ⥤ Rep R Γ` is the diagram of representations
  `(coveringAt D i).rep F`. `repCocone D R F` is its cocone with point
  `(action D R).rep F`, with legs the germ maps.
- `repCoconeIsColimit`: the germ cocone is a colimit in `Rep R Γ`. The forgetful functor
  to `ModuleCat R` reflects colimits, and the forgotten cocone is the colimit cocone of
  `V'.op ⋙ F.obj`.
- `injective_acyclic`: for finite `Γ` and an injective sheaf `Inj`, the cohomology
  `groupCohomology ((action D R).rep Inj) (n + 1)` vanishes. It combines
  `isZero_groupCohomology_of_isColimit` with the vanishing at each stage
  (`GaloisCovering.isZero_groupCohomology_rep_of_injective`).

## Assembly

`galoisCechSystemOfGerms` produces a `GaloisCechSystem (fun i => germ J R (obj i))` from:

- systems `obj : ι → I ⥤ C`;
- cover types, finite groups and target indices;
- germ Galois data `datum i c : GermGaloisDatum J (group i c) (obj (target i c)) (obj i)`;
- local lifting for the augmentations `(datum i c).aug R`.

The fields are filled as follows:

- the action and the augmentation from each datum;
- `aug_injective`, `aug_act` and `exists_aug_eq` from the lemmas above;
- `injective_acyclic` from `injective_acyclic`;
- `local_lift` from the supplied hypothesis.

## Scope

Nothing analytic is asserted. Several obligations of an analytic application remain
separate, and none of them is proved here:

- constructing the cofiltered systems and the germ Galois data;
- proving local lifting;
- comparing a germ functor with a point fibre of a direct image.

The last of these is not definitional in general, because `I` must be a `w`-small category.
