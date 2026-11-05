# Irreducible tempered representations are unitarizable

Author: Worker 6. Module `Langlands.Representation.Exponents.TemperedIrreducibleUnitarizableStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `TemperedIrreducibleUnitarizableStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.2.6, Corollary, printed p.232 / PDF p.238. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The corollary says: an irreducible tempered representation is unitary. Its proof: this follows from the Theorem of VII.2.6, because an irreducible square-integrable representation is unitary (IV.3.2) and parabolic induction preserves unitarity.

This is a **derived** formulation: temperedness is the published derived predicate `IsNormalizedExponentTempered`, and unitarity is the published algebraic predicate `Langlands.IsUnitarizable`.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`, as in the published temperedness predicate. For every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` with an arbitrary carrier universe `v`, it asserts that `π.IsIrreducible` and `IsNormalizedExponentTempered hG π` imply `IsUnitarizable π.representation`.

## The objects

- `SmoothRep.IsIrreducible` is simplicity of the lattice of invariant subspaces, including nonzeroness, with no finite-dimensionality.
- `Langlands.IsUnitarizable ρ` (`Langlands/Representation/Unitary/Basic.lean`) is the existence of a positive definite Hermitian form on the carrier that every `ρ(g)` preserves. No norm, topology, completion or finite-dimensionality is assumed. Renard's "unitaire" for a smooth representation means the existence of such an invariant inner product, as in the IV.3.2 statement that an irreducible square-integrable representation is unitary. The Hilbert-space completion is not part of the claim.

## Faithfulness notes

- Irreducibility is necessary. The remark after the corollary (printed p.232 / PDF p.238) says that without irreducibility the conclusion can fail. For example, a nonsplit self-extension of a unitary character of a split torus is tempered but not unitarizable, because an admissible unitarizable representation is semisimple. That remark is not formalized here.
- No admissibility, central character or finite length is assumed beyond temperedness, which includes admissibility.

## Remaining obligations

The proof is a separate obligation. The source route uses the Theorem of VII.2.6 (the companion statement unit `TemperedIrreducibleDiscreteSeriesStatement`): `π` embeds in `i_P^G σ` with `σ` irreducible and square-integrable modulo the center. Then:

- `σ` is unitarizable (IV.3.2): an invariant inner product is built from its square-integrable matrix coefficients on `M(F) ⧸ Z(M(F))`;
- the normalized induction of a unitarizable representation is unitarizable: the inner product `⟨f₁, f₂⟩ = ∫_K ⟨f₁(k), f₂(k)⟩ dk` over a good maximal compact `K` with `G = PK`, which uses the normalization by `δ_P^{1/2}` and the compactness of `P\G`;
- an invariant positive form restricts along an injective intertwiner (the published `InvariantPositiveForm.comap`).

## Provenance

This is a derived statement of the Corollary of VII.2.6 for the represented-parabolic interface. Temperedness is the published normalized-exponent predicate. Unitarity is the published algebraic unitarizability predicate.
