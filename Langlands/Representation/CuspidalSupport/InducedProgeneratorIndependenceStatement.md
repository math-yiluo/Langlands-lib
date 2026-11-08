# Independence of the induced progenerator: statement

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.InducedProgeneratorIndependenceStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.1: Lemma, Proposition and Corollary, printed p.207 / PDF p.213. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The progenerator `Π_D` is that of VI.4.1, printed p.149 / PDF p.155.

## The source

Let `Ω` be a connected component of `Ω(G)` and `(M, (ρ, W))` a cuspidal datum in `Ω`, with `M` a standard Levi subgroup, Levi factor of the standard parabolic `P = MN`. Let `D = [M, (ρ, W)]_M` be the inertial class of `ρ` in `M`, and `Π_D` the progenerator of `M(M)_D` built in VI.4.1. There, for an irreducible supercuspidal `π` of `M`, `Π = ind_{⁰M}^M(ρ₀)`, where `ρ₀` is one of the irreducible summands of the restriction of `π` to `⁰M`. Renard then shows:

- **Lemma.** If `M` is maximal and `w` is the nontrivial element of `W(M, *)`, `M' = w · M`, `D' = w · D` and `P'` is the standard parabolic with Levi `M'`, then `i_P^G(Π_D) ≃ i_{P'}^G(Π_{D'})`. The isomorphism is not canonical.
- **Proposition.** The same holds for every `w ∈ W(M, *)`.
- **Corollary.** For every `P' ∈ P(M)`, `i_P^G(Π_D) ≃ i_{P'}^G(Π_D)`.

The consequence drawn on printed p.208 is that the isomorphism class of `Π_Ω = i_P^G(Π_D)` does not depend on the datum `(M, D)` used to build it.

## The Lean statement

`InducedProgeneratorIndependenceStatement` combines the three results into one derived statement for actual groups. It is a statement unit: nothing is proved.

It quantifies over:

- a nonarchimedean local field `k : Type u` (`[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`), of any characteristic;
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`, whose rational points carry the canonical topology `RationalPointFamily.pointTopology` and are assumed locally compact and nonarchimedean;
- two actual rational parabolics `P = MN` (`p`, `l`, `r` with `hp`, `hl`, `hr`, `hmul`) and `P' = M'N'` (`p'`, `l'`, `r'` with the same four hypotheses), neither assumed standard;
- `g : rationalPoints G` and a group-scheme isomorphism `φ : M ≅ M'` with `φ.hom ≫ l' ≫ p' = l ≫ p ≫ (G.innerIso g).hom`. Since the published `innerIso g` is conjugation by `g`, this says that `g ι(m) g⁻¹ = ι'(φ m)` for the embeddings `ι = l ≫ p` and `ι' = l' ≫ p'`: conjugation by `g` carries `M` onto `M'`, and `φ` is the induced isomorphism;
- a topological group isomorphism `e : rationalPoints M' ≃ₜ* rationalPoints M` equal to `φ⁻¹` on rational points;
- `π : SmoothRep.{0, u, v} ℂ (rationalPoints M)`, irreducible and supercuspidal (the published `IsSupercuspidal`: all normalized Jacquet modules along proper actual parabolics of `M` vanish);
- `ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M)`, irreducible, with an injective morphism `j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π`. Here `Plancherel.rationalCommonNormKernel M` is the common kernel of the norms of all rational characters of `M`, Renard's `⁰M`, as a subgroup of `M(F)`. These are exactly the hypotheses of the published VI.4.1 statement `CuspidalSupport.RationalSummandSmallProgeneratorStatement`, applied to the group `M`.

The rational points of `M` and `M'` carry the canonical Levi topologies `leviPointTopology`, which are definitionally the canonical topologies used by the VI.4.1 construction. `Π_D` is the published `CuspidalSupport.rationalNormKernelSummandInduction M ρ₀`, the compact induction `ind_{⁰M(F)}^{M(F)} ρ₀`, a smooth representation of `M(F)` on a carrier in `Type (max u v)`.

The conclusion is

`Nonempty (i_P^G(Π_D) ≅ i_{P'}^G(SmoothRep.pullback e Π_D))`,

an isomorphism in `SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` between the published normalized inductions `leviInductionFunctor`. The representation `SmoothRep.pullback e Π_D` of `M'(F)` is `m' ↦ Π_D(φ⁻¹ m')`, i.e. `m' ↦ Π_D(g⁻¹ m' g)`. In Renard's convention `(w · σ)(m') = σ(w⁻¹ m' w)`, this is `w · Π_D`, which is isomorphic to `Π_{w · D}`. Indeed, conjugation carries `⁰M` onto `⁰M'` and `ρ₀` to an irreducible summand `w · ρ₀` of `(w · π)|_{⁰M'}`, and compact induction commutes with this transport. This identification is a remark and is not formalized. Only existence of an isomorphism is asserted, as in the source.

## Relation to the three source results

- The **Corollary** is the case `g = 1`, `M' = M`, `φ = 𝟙`, with `P'` any parabolic with the same Levi embedding.
- The **Proposition** is the case where `M`, `P`, `P'` are standard and `g` represents `w ∈ W(M, *)` with `w · M = M'`. The **Lemma** is the subcase of a maximal `M`.
- Conversely, the general statement follows from the Corollary. Write `P'' = g P g⁻¹`, a parabolic with Levi `M'`. Then `f ↦ f(g⁻¹ ·)` identifies `i_P^G(σ)` with `i_{P''}^G(σ ∘ φ⁻¹)`, and the Corollary for `M'` compares `P''` with `P'`. So the derived statement claims no more than the three source results.

The source's parabolics are standard, as is customary in Renard. The actual-group statement allows arbitrary parabolics and any conjugating element. No Weyl group of actual groups is needed.

## Remarks

- The proof (VII.1.3 Corollary, the geometric lemma VI.5.3 and transitivity of induction) is not formalized here.
- The VI.10.1 Theorem, that `Π_Ω` is a finitely generated progenerator of `M(G)_Ω`, is a separate unit. It needs the Bernstein block `M(G)_Ω` of `G` together with the second adjointness theorem.
