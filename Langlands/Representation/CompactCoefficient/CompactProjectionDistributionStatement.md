# The idempotents `e_{K,τ}` of an irreducible compact representation: statement

Author: Worker 6. Module `Langlands.Representation.CompactCoefficient.CompactProjectionDistributionStatement`, namespace `Langlands.Renard.CompactRepresentation`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, IV.1.5, Theorem and proof, printed p.92 / PDF p.98, in the setting of IV.1.3–IV.1.4 (`G` a unimodular t.d. group, countable at infinity, with a bi-invariant Haar measure). The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

Let `(τ, W)` be an irreducible compact representation of `G` and `K` a compact open subgroup. The theorem reads:

- (i) There is a unique distribution `e_{K,τ} ∈ H(G)` such that `τ(e_{K,τ}) = τ(e_K)` and `ρ(e_{K,τ}) = 0` for every irreducible smooth representation `(ρ, E)` of `G` not equivalent to `(τ, W)`.
- (ii) If `K'` is a compact open subgroup contained in `K`, then `e_{K',τ} ∗ e_{K,τ} = e_K ∗ e_{K',τ} = e_{K',τ} ∗ e_K = e_{K,τ}`. In particular `e_{K,τ}` is idempotent.
- (iii) For `g ∈ G`, `δ_g ∗ e_{K,τ} ∗ δ_{g⁻¹} = e_{gKg⁻¹,τ}`.

Renard identifies `H(G)` with `𝒟(G)` through the chosen Haar measure (IV.1.4).

## The Lean statement

`CompactProjectionDistributionStatement` is a statement unit: nothing is proved.

**Group and measure.** The binders are those of the published Bernstein–Zelevinsky statements (`CompactCoefficientProjectorStatement`). `G : Type u` is a Hausdorff, locally compact, totally disconnected topological group that is `SigmaCompactSpace`. It carries its Borel structure and a regular Haar measure `μ` that is also right invariant (unimodularity).

**The Hecke algebra.** `H(G)` is the published `Hecke.HeckeAlgebra μ`: compactly supported locally constant functions with `μ`-convolution, Renard's identification of `H(G)` with `𝒟(G)`. A smooth representation acts through the published `Hecke.heckeAction μ ρ hρ`, a non-unital algebra homomorphism to the linear endomorphisms. `e_K` is the published `Hecke.HeckeAlgebra.normalizedIndicator μ K hK = μ(K)⁻¹ 1_K`.

**Hypotheses on `τ`.** `τ : SmoothRep.{0, u, v} ℂ G` is irreducible and has compactly supported smooth coefficients (the published `HasCompactSmoothDualCoefficients`). This is Renard's compactness by IV.1.3.

**The predicate.** Inside the statement, `IsProjector K hK e`, for an open subgroup `K` with `hK : IsCompact (K : Set G)` and `e : Hecke.HeckeAlgebra μ`, means:

- `heckeAction τ e = heckeAction τ (normalizedIndicator μ K hK)`, and
- `heckeAction ρ e = 0` for every irreducible `ρ : SmoothRep.{0, u, v} ℂ G` with `IsEmpty (ρ ≅ τ)`.

The conclusion is the conjunction of:

1. **(i)** for every compact open `K`, `∃! e, IsProjector K hK e`;
2. **(ii)** for compact open `K' ≤ K` and `e`, `e'` with `IsProjector K hK e` and `IsProjector K' hK' e'`: `e' * e = e`, `normalizedIndicator K * e' = e` and `e' * normalizedIndicator K = e`;
3. **(iii)** for `g : G`, compact open `K` and `K'` with `x ∈ K' ↔ g⁻¹ x g ∈ K` (so `K' = gKg⁻¹`), and `e` with `IsProjector K hK e`, the function `x ↦ e(g⁻¹ x g)` satisfies `IsProjector K' hK'`. This function is `TestFunction.rightTranslate g (TestFunction.leftTranslate g e)`, transported back to `HeckeAlgebra μ`. With the published conventions `(L_g f)(x) = f(g⁻¹ x)` and `(R_g f)(x) = f(x g)`, it is `δ_g ∗ e ∗ δ_{g⁻¹}` for the unimodular measure.

By (i), `e_{K,τ}` is the unique `e` with `IsProjector K hK e`. So (ii) and (iii) are Renard's identities, stated for any elements satisfying the defining property.

## Remarks

- The irreducible representations `ρ` range over carriers in the universe `v` of `τ`. This loses nothing for a group countable at infinity, since irreducible smooth representations have countable dimension and so have copies in every universe. The uniqueness in (i) relies on the completeness theorem III.1.11 for these representations.
- The operator `π(e_τ)` built from these idempotents, the formal degree `d(τ)` and the IV.1.4 Proposition are not stated here. The projector `π(e_τ)` on arbitrary smooth representations corresponds to the published `CompactCoefficientProjectorStatement`.
- The proof is not formalized here.
