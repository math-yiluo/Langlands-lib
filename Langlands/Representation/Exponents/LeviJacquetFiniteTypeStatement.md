# Normalized parabolic restriction preserves finite type

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviJacquetFiniteTypeStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviJacquetFiniteTypeStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.1.3, Proposition, printed p.136 / PDF p.142, with its proof on the same page. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the Proposition says: let `P = MN` be a parabolic subgroup of `G` and `(π, V)` a smooth representation of finite type of `G`; then `(π_N, V_N)` is of finite type, and so is `r_P^G(π, V)`.

This is a **derived** formulation. The Jacquet module is the published normalized `leviJacquetFunctor`, a representation of `M(F)`. Only the normalized assertion is stated; see "Faithfulness notes" for the unnormalized one.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over every actual rational parabolic `p : P ⟶ G` with `hp : IsParabolicSubgroup p`, every rational Levi `l : M ⟶ P` with `hl : IsRationalLeviSubgroup l`, and every matching geometric unipotent radical `r : U ⟶ P` with `hr` and `hmul : IsIso (subgroupMultiplication l r)`.

For these data it installs on `rationalPoints M` the affine instance `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl` from the published Levi-point interface `ArbitraryParabolicLeviPoints`.

Then, for every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` with an arbitrary carrier universe `v`, it asserts that

`Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule`

implies

`Module.Finite (MonoidAlgebra ℂ (rationalPoints M)) ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.asModule`.

## The objects

- Finite type. A smooth representation is of finite type when finitely many vectors generate it as a representation. This is finite generation of the carrier as a module over the group algebra `ℂ[G(F)]` (`MonoidAlgebra`), through Mathlib's `Representation.asModule`. The Library uses the same convention elsewhere, for example in `Exponents/SplitComponentFiniteSupport.lean`.
- `leviJacquetFunctor p l r hp hr hl hmul` is the published normalized Jacquet functor `r_P^G`. It takes the coinvariants for the radical image `pointImage (r ≫ p)` with the descended action of the Levi image, twisted by the inverse square root of the usual Haar modulus, and pulls back along `leviPointsEquiv p l hp hl : M(F) ≃ₜ* pointImage (l ≫ p)`. Renard's `δ_P` is the inverse of the usual modulus, so this twist is Renard's `δ_P^{1/2}` in (VI.1.2.2), printed p.135 / PDF p.141.

## Faithfulness notes

- The Proposition is stated for every parabolic `P = MN`. The statement quantifies over every actual rational parabolic with a rational Levi and a matching radical, not only standard ones.
- No admissibility, finite length or irreducibility is assumed.
- The source's first assertion, finite type of the unnormalized `(π_N, V_N)`, is not stated separately. The normalized and unnormalized modules have the same carrier, and the actions differ by a character of `M(F)` with values in `ℂˣ`. Hence the same vectors generate both, which is the source's remark "la normalisation n'y change rien".
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses. Those of `M(F)` are derived from them, not assumed.

## Remaining obligations

The proof is a separate obligation. The source proof chooses a compact open subgroup `K` fixing a finite generating set, uses that `P\G/K` is finite because `P\G` is compact, and observes that the images in `V_N` of the translates of the generators by representatives of `P\G/K` generate `V_N` over `M`.

The published `Langlands.Aubert.General.jacquetFiniteGenerationOfCompactQuotient` proves `JacquetFiniteGenerationOfCompactQuotientStatement`. That statement is this argument for an abstract semidirect decomposition `P = M ⋉ U`, with compactness of the quotient `Induction.LeftQuotient P` as a hypothesis. A proof of this statement along that route needs:

- compactness of `Induction.LeftQuotient (pointImage p)`, which is the published `ArbitraryParabolicQuotientCompactStatement` (Renard V.5.1 Corollary); its proof is the separate task `c1ce4629-6768-4eb5-b4ee-0086526913ea`;
- closedness of the radical image, from the published `isClosed_pointImage_comp`;
- the transport of finite generation across `leviPointsEquiv`, which identifies `ℂ[M(F)]`-modules with `ℂ[pointImage (l ≫ p)]`-modules on the same carrier.

None of these is asserted here.

## Provenance

This is a derived statement of the Proposition of VI.1.3 for the represented-parabolic interface. Finite type is finite generation over the group algebra. The Jacquet module is the published normalized `leviJacquetFunctor`, linked to the Levi image by the published `leviPointsEquiv`. The unnormalized assertion is equivalent, as explained above, and is not stated separately.
