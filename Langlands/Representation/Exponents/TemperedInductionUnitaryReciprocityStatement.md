# Tempered Frobenius reciprocity through the unitary Jacquet part

Author: Worker 6. Module `Langlands.Representation.Exponents.TemperedInductionUnitaryReciprocityStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `TemperedInductionUnitaryReciprocityStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.2.4, Proposition, printed p.229 / PDF p.235. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the Proposition says: let `P = MN` be a parabolic subgroup of `G`; for every tempered representation `(σ, E)` of `M` and every tempered representation `(π, V)` of `G` there is a natural isomorphism

`Hom_G(V, i_P^G E) ≃ Hom_M((r_P^G V)_0, E)`.

The proof says that the result is the conjunction of Frobenius reciprocity VI.1.1 and Lemma III.1.10.

This is a **derived** formulation, for four reasons. Temperedness is the published derived predicate `IsNormalizedExponentTempered`. `(r_P^G V)_0` is the published `leviUnitaryJacquetModule`. The isomorphism is stated as an explicit linear bijection given by evaluation at the identity (see "The isomorphism"). The parabolic is any actual rational parabolic. The published statement `TemperedJacquetUnitaryRestrictionStatement` states only the second step of the source proof. This statement is the full Proposition.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology, as in the published temperedness predicate. It then quantifies over the following data:

- every actual rational parabolic `p : P ⟶ G` with `hp : IsParabolicSubgroup p`;
- every rational Levi `l : M ⟶ P` with `hl : IsRationalLeviSubgroup l`;
- every matching geometric unipotent radical `r : U ⟶ P` with `hr` and `hmul : IsIso (subgroupMultiplication l r)`;
- every split component `a : A.toGrp ⟶ M` with `ha : IsSplitComponent a`.

For these data it installs on `rationalPoints M` the affine instance `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl` from the published Levi-point interface `ArbitraryParabolicLeviPoints`.

Then, for every `π : SmoothRep.{0, u, w} ℂ (rationalPoints G)` and every `σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)`, with independent carrier universes `w` and `v`, it asserts the following. If `IsNormalizedExponentTempered hG π` and `IsNormalizedExponentTempered hl.isConnectedReductive σ` hold, then there is a `ℂ`-linear equivalence

`e : Hom_G(π, i_P^G σ) ≃ₗ[ℂ] Hom_M((r_P^G π)_0, σ)`

between the spaces of intertwining maps (`Representation.IntertwiningMap`), from `π` to `(leviInductionFunctor p l r hp hr hl hmul).obj σ` and from `leviUnitaryJacquetModule p l r hp hl hr hmul ha π` to `σ`. It satisfies the following: for every intertwiner `F`, every vector `y` of the unitary part and every vector `x` of `π`, if the image of `y` under `leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π` is the Jacquet class `Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x`, then

`e F y = (F x)(1)`,

where `(F x)(1)` is `Induction.eval (pointImage p) (inducingRepresentation …) (F x) 1`.

## The objects

- `leviInductionFunctor p l r hp hr hl hmul` is the published normalized parabolic induction `i_P^G` on representations of `M(F)`. It pulls `σ` back along the inverse of `leviPointsEquiv p l hp hl : M(F) ≃ₜ* pointImage (l ≫ p)` and applies the published `inductionFunctor` from the Levi image. Its elements are smooth functions `f` on `G(F)` with `f(x g) = δ(x)^{1/2} σ'(proj x) f(g)` for `x` in the parabolic image. Here `σ'` is the pulled-back representation, `proj` is the Levi projection and `δ` is the usual Haar modulus. Renard's `δ_P` is the inverse of the usual modulus (remark after (VI.1.2.2), printed p.136 / PDF p.142), so this is Renard's (VI.1.2.3). `inducingRepresentation …` is the representation `x ↦ δ(x)^{1/2} σ'(proj x)` of the parabolic image, and `Induction.eval (pointImage p) _ f 1` is `f(1)`.
- `leviJacquetFunctor p l r hp hr hl hmul` is the published normalized Jacquet functor `r_P^G` with values in representations of `M(F)`. Its carrier is the quotient of coinvariants `V_N`, and `Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x` is the class of `x`.
- `unitaryJacquetPart p l r hp hl hr hmul ha π` is the published `(r_P^G V)_0`: the sum of the characteristic spaces of the split component `A_M(F)` for the normalized exponents with vanishing normalized real part. `leviUnitaryJacquetModule p l r hp hl hr hmul ha π` is this subrepresentation as a smooth representation of `M(F)`, and `leviUnitaryJacquetModuleι` is its inclusion into `(leviJacquetFunctor …).obj π`.
- `IsNormalizedExponentTempered` is the published temperedness predicate, for `G` and for the connected reductive Levi `M`. Its Markdown explains its derivation from the definition at the start of VII.2.1 (printed p.227 / PDF p.233). It includes admissibility.

## The isomorphism

Every element of the Jacquet module is a class `[x]`, so every `y` in the unitary part satisfies the hypothesis of the formula for some `x`. The formula therefore determines `e F` on the whole unitary part, and `e` is unique. In terms of the published inclusion, `e F` is the restriction to `(r_P^G π)_0` of the Frobenius map `[x] ↦ (F x)(1)` on `r_P^G π`. That map is the explicit adjunction of VI.1.2, staged separately as `LeviFrobeniusReciprocityStatement`. The source's "natural" is not stated as a separate clause. Naturality in `π` and in `σ` follows from the formula by the same direct computation as for Frobenius reciprocity, which is not carried out here.

## Faithfulness notes

- The Proposition is stated for every parabolic `P = MN`. The statement quantifies over every actual rational parabolic with a rational Levi, a matching radical and a split component, not only standard ones.
- The source's `σ` and `π` are arbitrary tempered representations. Temperedness includes admissibility, so no further hypothesis is added. No irreducibility, finite length or central character is assumed.
- The carrier universes of `π` and `σ` are independent. The induced representation has carrier universe `max u v`, and the unitary part has the carrier universe `w` of `π`.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses, as in the published temperedness predicate. Those of `M(F)` are derived from them, not assumed.

## Remaining obligations

The proof is a separate obligation. Along the source route it needs:

- Frobenius reciprocity for the normalized functors (VI.1.2, staged as `LeviFrobeniusReciprocityStatement`). This in turn needs the unimodularity of the radical `N(F)`;
- the restriction step, in the form of the published `TemperedJacquetUnitaryRestrictionStatement`. That statement takes `π` and `σ` in one carrier universe, so a proof for independent universes `w` and `v` must either reprove the step or transport carriers;
- the decomposition `r_P^G π = (r_P^G π)_0 ⊕ (r_P^G π)_+` (published statement `UnitaryJacquetPartTemperedStatement`), together with unitarity of the exponents of a tempered `σ` relative to its own split component (VII.2.1, Remark 1; Lemma III.1.10, printed p.63 / PDF p.69, for characteristic spaces of a central subgroup);
- existence of compatible root presentations for the parabolic triples involved, which the published temperedness predicate needs to make its cone condition effective.

None of these is asserted here.

## Provenance

This is a derived statement of the Proposition of VII.2.4 for the represented-parabolic interface. Temperedness on both sides is the published normalized-exponent predicate. `(r_P^G V)_0` is the published unitary Jacquet part. The isomorphism is the explicit evaluation-at-identity bijection, which determines it and implies its naturality. The representation of `M` is a representation of `M(F)`, linked to the Levi image by the published `leviPointsEquiv`.
