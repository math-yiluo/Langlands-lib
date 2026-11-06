# Homomorphisms from the Jacquet module to a tempered representation

Author: Worker 6. Module `Langlands.Representation.Exponents.TemperedJacquetUnitaryRestrictionStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `TemperedJacquetUnitaryRestrictionStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.2.4, Proposition, printed p.229 / PDF p.235. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The Proposition says: let `P = MN` be a parabolic subgroup of `G`; for every tempered representation `(σ, E)` of `M` and every tempered representation `(π, V)` of `G` there is a natural isomorphism

`Hom_G(V, i_P^G E) ≃ Hom_M((r_P^G V)_0, E)`.

The proof is one line: "this result is the conjunction of Frobenius reciprocity VI.1.1 and Lemma III.1.10". Frobenius reciprocity gives `Hom_G(V, i_P^G E) ≃ Hom_M(r_P^G V, E)`. Lemma III.1.10 (printed p.63 / PDF p.69) says that there are no nonzero intertwiners between smooth representations with distinct central characters. Applied to the characteristic spaces of the split component `A_M`, which is central in `M`, it identifies `Hom_M(r_P^G V, E)` with `Hom_M((r_P^G V)_0, E)`, because `E` has only unitary exponents.

This is a **derived partial** formulation. It states the second step exactly, as a bijection given by restriction along the inclusion `(r_P^G V)_0 → r_P^G V`. It does not state the Frobenius step; see "Scope" below.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology, as in the published temperedness predicate. It then quantifies over every actual rational parabolic `p : P ⟶ G` with `hp : IsParabolicSubgroup p`, every rational Levi `l : M ⟶ P` with `hl : IsRationalLeviSubgroup l`, every matching geometric unipotent radical `r : U ⟶ P` with `hr` and `hmul : IsIso (subgroupMultiplication l r)`, and every split component `a : A.toGrp ⟶ M` with `ha : IsSplitComponent a`.

For these data it installs on `rationalPoints M` the affine instance `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl` from the published Levi-point interface `ArbitraryParabolicLeviPoints`.

Then, for every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` and every `σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)`, it asserts that `IsNormalizedExponentTempered hG π` and `IsNormalizedExponentTempered hl.isConnectedReductive σ` imply that the map

`f ↦ leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π ≫ f`

from morphisms `(leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶ σ` to morphisms `leviUnitaryJacquetModule p l r hp hl hr hmul ha π ⟶ σ` is bijective. The morphisms are those of the smooth-representation category of `M(F)`, i.e. `M(F)`-intertwining linear maps.

## The objects

- `(leviJacquetFunctor p l r hp hr hl hmul).obj π` is the published normalized Jacquet module `r_P^G π`, transported to a representation of `M(F)` along `leviPointsEquiv p l hp hl`.
- `leviUnitaryJacquetModule … π` is Renard's `(r_P^G π)_0`, the sum of the characteristic spaces of the split component over the exponents with zero real part, as a representation of `M(F)`. `leviUnitaryJacquetModuleι … π` is its inclusion into the transported Jacquet module. Both are defined in `ArbitraryParabolicUnitaryJacquetPart`.
- `IsNormalizedExponentTempered` is the published temperedness predicate, for `G` and for the connected reductive group `M`.

The carrier universes of `π` and `σ` are both `v`, since the transported Jacquet module of `π` has the carrier universe of `π` and morphisms need a common universe.

## Scope

The source proposition composes this bijection with Frobenius reciprocity VI.1.1. The statement here omits that step for two reasons:

- No represented-parabolic Frobenius reciprocity exists yet for `leviInductionFunctor` and `leviJacquetFunctor`. The published `Langlands.Aubert.General.FirstAdjointness.equiv` gives `Hom(A, i σ) ≃ Hom(r A, σ)` for an abstract semidirect decomposition of subgroups, under the explicit premise `IsUnimodularModulus` on the radical. Applying it here needs that unimodularity for the rational points of an actual unipotent radical, which follows from V.5.2(iii) (the radical is a union of compact open subgroups), and the transport of morphisms between the Levi image and `M(F)`.
- With those inputs, the proposition is the composite of `FirstAdjointness.equiv` with the bijection stated here. Its naturality in `π` and `σ` follows from the naturality of both maps.

So this statement covers exactly the representation-theoretic content that VII.2.4 adds to VI.1.1. A statement of the composite isomorphism is a separate unit, once represented-parabolic Frobenius reciprocity is available.

## Faithfulness notes

- The parabolic is arbitrary, as in the source. The statement quantifies over every actual rational parabolic with a rational Levi, a matching radical and a split component.
- No hypotheses beyond the source's temperedness of `σ` and `π` are added. Irreducibility, finite length and central characters are not assumed. Temperedness includes admissibility.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses, as in the published temperedness predicate. Those of `M(F)` are derived from them.

## Remaining obligations

The proof is a separate obligation. A proof along the source route needs:

- the decomposition `r_P^G π = (r_P^G π)_0 ⊕ (r_P^G π)_+` into `M(F)`-subrepresentations, from (VII.1.1.1) for the admissible `π` (published statement `ArbitraryParabolicExponentStatement`). This gives surjectivity, by extending by zero on `(r_P^G π)_+`;
- that an `M(F)`-intertwiner maps the characteristic space of a character `χ` of the split component into the characteristic space of `χ` in `σ`, since the split component acts centrally in `M(F)`;
- that `σ` has no nonzero characteristic space for a character with nonzero real part. This is the unitarity of the exponents of a tempered representation relative to its own split component (VII.2.1, Remark 1), from the temperedness condition for the trivial parabolic `M ⊂ M`, whose closed cone is `{0}`. Together with the previous point this gives injectivity. This is the form of Lemma III.1.10 for characteristic spaces of a central subgroup, not only for central characters;
- existence of a compatible root presentation for the trivial parabolic of `M`, which the published predicate needs to make its cone condition effective.

## Provenance

This is a derived partial statement of the Proposition of VII.2.4 for the represented-parabolic interface. It states the restriction bijection `Hom_M(r_P^G π, σ) ≃ Hom_M((r_P^G π)_0, σ)`. Combined with Frobenius reciprocity VI.1.1, this bijection gives the source's isomorphism. Temperedness is the published normalized-exponent predicate. Representations of `M` are representations of `M(F)`, linked to the Levi image by the published `leviPointsEquiv`.
