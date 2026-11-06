# The unitary part of the Jacquet module of a tempered representation

Author: Worker 6. Module `Langlands.Representation.Exponents.UnitaryJacquetPartTemperedStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `UnitaryJacquetPartTemperedStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.2.3, Lemma, printed p.229 / PDF p.235, with its proof on the same page. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The lemma says: let `(π, V)` be a tempered representation of `G` and `P = MN` a standard parabolic subgroup. Decompose the Jacquet module as a direct sum of representations of `M`,

`r_P^G V = (r_P^G V)_0 ⊕ (r_P^G V)_+`,

where `(r_P^G V)_0` is the sum of the characteristic spaces `(r_P^G V)_χ` over the exponents `χ ∈ Exp(A_M, r_P^G V)` with `ℜ(χ) = 0`, and `(r_P^G V)_+` is the sum over those with `ℜ(χ) ≠ 0`. Then `(r_P^G π)_0` is a tempered representation of `M`.

This is a **derived** formulation. Temperedness is the published derived predicate `IsNormalizedExponentTempered`, the parabolic is arbitrary instead of standard, and the direct-sum decomposition, which the source takes from VII.1.1, is part of the conclusion. These choices are explained below.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology, as in the published temperedness predicate. It then quantifies over every actual rational parabolic `p : P ⟶ G` with `hp : IsParabolicSubgroup p`, every rational Levi `l : M ⟶ P` with `hl : IsRationalLeviSubgroup l`, every matching geometric unipotent radical `r : U ⟶ P` with `hr` and `hmul : IsIso (subgroupMultiplication l r)`, and every split component `a : A.toGrp ⟶ M` with `ha : IsSplitComponent a`.

For these data it installs on `rationalPoints M` the affine instance `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the local-compactness and nonarchimedean-group instances `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl`, all from the published Levi-point interface `ArbitraryParabolicLeviPoints`.

Then, for every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` with an arbitrary carrier universe `v`, it asserts that `IsNormalizedExponentTempered hG π` implies the conjunction of

1. `IsCompl (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule`: the two parts are complementary subspaces of the normalized Jacquet module, which is Renard's direct sum `r_P^G V = (r_P^G V)_0 ⊕ (r_P^G V)_+`;
2. `IsNormalizedExponentTempered hl.isConnectedReductive (leviUnitaryJacquetModule p l r hp hl hr hmul ha π)`: the unitary part, as a smooth representation of `M(F)`, is tempered.

## The objects

- `unitaryJacquetPart` and `nonunitaryJacquetPart` are defined in `ArbitraryParabolicUnitaryJacquetPart`. They are the suprema, in the lattice of subrepresentations of the published normalized Jacquet module `(jacquetFunctor p l r hp hr hl hmul).obj π`, of the published weight spaces `normalizedJacquetWeightSpace … χ` over the published exponents `χ` with `normalizedRealPart … χ = 0`, respectively `≠ 0`. Their underlying subspaces are the sums of the characteristic spaces, as in the source. The real part is the `q^(-s)` parameter `Plancherel.SplitTorus.normalizedRealPart`. Renard's raw-log real part is `-log q` times it, so `ℜ(χ) = 0` has the same meaning for both.
- `leviUnitaryJacquetModule` is the unitary part as a subrepresentation of the Jacquet module, pulled back to `M(F)` along `leviPointsEquiv p l hp hl : M(F) ≃ₜ* pointImage (l ≫ p)`. This is Renard's representation `(r_P^G π)_0` of `M`.
- `IsNormalizedExponentTempered hl.isConnectedReductive _` is the published temperedness predicate for the connected reductive group `M`, with the canonical topology on `M(F)`. Its parabolics, Levi subgroups and split components are those of `M`.

## Temperedness

The published predicate `IsNormalizedExponentTempered` is a derived formulation of the definition at the start of VII.2.1 (printed p.227 / PDF p.233). It requires admissibility. It also requires, for every actual rational parabolic, rational Levi and split component, that a compatible root presentation exist and that every normalized Jacquet exponent have its `q^(-s)` real part in the closed root cone `pres.nonnegCone` of every compatible presentation. The predicate's own Markdown records why the `q^(-s)` real part is used instead of the raw-log parameter that V.3.20 also writes. This statement uses the predicate unchanged for `G` and for `M`.

## Faithfulness notes

- **Every parabolic.** The source lemma takes `P` standard. The statement quantifies over every actual rational parabolic with a rational Levi, a matching radical and a split component. The general case is the expected extension: every parabolic is `G(F)`-conjugate to a standard one, and conjugation transports the Jacquet module, its exponents, its two parts and temperedness. This reduction is part of the proof obligation, not something asserted here.
- **The direct sum.** The source writes "décomposons le module de Jacquet en une somme directe" and takes the decomposition from (VII.1.1.1) for admissible representations. A tempered representation is admissible, so the decomposition applies. The statement records it as the first conjunct. It follows from the published VII.1.1 statement `ArbitraryParabolicExponentStatement`, which gives the independence and the spanning of the characteristic spaces of an admissible representation. Each exponent has either zero or nonzero real part.
- **No other hypotheses.** No irreducibility, finite length, central character or finite-dimensionality is assumed. The source's `π` is any tempered representation, and temperedness includes admissibility.
- **Topology.** The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses, as in the published temperedness predicate. Those of `M(F)` are derived from them, not assumed.

## Remaining obligations

The proof is a separate obligation. The source proof fixes an exponent `χ` with `ℜ(χ) = 0`. A standard parabolic of `M` is `M ∩ Q` for a standard parabolic `Q = LU ⊂ P` of `G`. By transitivity of the restriction functors (VI.1.4), every normalized exponent `χ_Q` of `(r_P^G π)_χ` relative to `M ∩ Q` is a normalized exponent of `π` relative to `Q`, so `ℜ(χ_Q) ∈ ^+[𝔞_L^*]^G_Q` by temperedness of `π` (VII.2.3.1). By Lemma VII.1.1(ii) the restriction of `χ_Q` to `A_M` is `χ`. With the decomposition `𝔞_L^* = 𝔞_M^* ⊕ (𝔞_L^M)^*` of V.3.13, the projection of `ℜ(χ_Q)` to `𝔞_M^*` is `ℜ(χ) = 0`. Hence `ℜ(χ_Q) ∈ (𝔞_L^M)^* ∩ ^+[𝔞_L^*]^G_Q ⊂ ^+[(𝔞_L^M)^*]^M_{Q∩M}`.

A Lean proof also needs these facts, none of which is asserted here:

- the Jacquet module of an admissible representation is admissible, so `(r_P^G π)_0` is admissible;
- a compatible root presentation exists for every actual parabolic triple of `M`, as the predicate requires;
- the parabolics of `M` correspond to parabolics of `G` contained in `P`, compatibly with the transport between `M(F)` and the Levi image;
- the transitivity isomorphism of VI.1.4 for the published normalized Jacquet functors, and its compatibility with the split components;
- the comparison of the closed root cones of `G` relative to `Q` and of `M` relative to `M ∩ Q` on `(𝔞_L^M)^*`.

## Provenance

This is a derived statement of the Lemma of VII.2.3 for the represented-parabolic interface. Temperedness of `π` and of `(r_P^G π)_0` is the published normalized-exponent predicate. The representation `(r_P^G π)_0` of `M` is a representation of `M(F)`, linked to the Levi image of the parabolic by the published `leviPointsEquiv`. The extension from standard to arbitrary parabolics and the explicit direct-sum conjunct are formalization choices explained above.
