# Fourier inversion on `A_G` for `p_χ` (Waldspurger, proof of Theorem VIII.1.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralFourierInversion`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.DiscreteFourierUniqueness` (submitted together with this
  module): `characterSum`, `countable_of_fg` and `eq_zero_of_characterSum_eq_zero`
  (uniqueness of Fourier coefficients on a finitely generated commutative group);
- `CentralProjection`: `centralProjection` (Waldspurger's `p_χ`), `CentralWeights` and
  `CentralWeights.integrable_of_mem_level`; through it `Basic` (`CompactOpenSubgroup`,
  `schwartzSubmodule`, `levelSubmodule`, `IsBiInvariant`, `mem_schwartzSubmodule_iff`).

From Mathlib it uses `MeasureTheory.hasSum_integral_iUnion`,
`MeasureTheory.setIntegral_congr_fun`, `MeasureTheory.setIntegral_const`,
`MeasureTheory.measure_preimage_mul`, `QuotientGroup.discreteTopology`,
`QuotientGroup.continuous_mk`, `QuotientGroup.eq`, `QuotientGroup.out_eq'`,
`Subgroup.mem_sup_of_normal_right`, `MonoidHom.map_closure`, `Group.fg_iff`,
`Subgroup.coe_subgroupOf` and `IsClosed.isClosedEmbedding_subtypeVal`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus 234.

- End of VIII.5, proof of Theorem VIII.1.1, printed p. 332 (PDF p. 98): "Supposons `φ ≠ 0`.
  Par inversion de Fourier sur le groupe `A_G`, il existe `χ ∈ Â_G` tel que `p_χ φ ≠ 0`."
  Here `φ ∈ °C(G) ⊂ C(G)`.
- VIII.4, printed p. 327 (PDF p. 93): "Notons `Â_G` l'ensemble des caractères unitaires de
  `A_G`, i.e. `Â_G = {χ ∈ Hom(A_G, ℂ^×); Re(χ) = 0}`", and `(p_χ f)(g) = ∫_{A_G} χ⁻¹(a) f(ag) da`
  for `f ∈ C(G)`, an absolutely convergent integral.
- I.1, printed p. 239 (PDF p. 5): "On note `Hom(G, ℂ*)` le groupe des homomorphismes continus
  de `G` dans `ℂ*`", and `A_M` is "le plus grand tore déployé dans le centre de `M`" (for
  `M = G`, `A_G`). By the convention of printed p. 238, a split torus `A` stands for its group
  of `F`-points.

So `Â_G` is the set of continuous characters `A_G → ℂ^×` of absolute value one. This is the
class of characters quantified over in `eq_zero_of_forall_centralProjection_eq_zero`.
Waldspurger does not give a proof of the Fourier inversion step; the proof here is derived.

## Scope: abstract data and explicit hypotheses

The module proves the contrapositive of Waldspurger's sentence for abstract data: if
`p_χ f = 0` for every `χ ∈ Â_G`, then `f = 0`. It does not construct `A_G` or its Haar
measure, and it does not prove that `A_G` satisfies `HasFGCompactOpenQuotients` (see Open
obligations).

**Section `Coset`.** `Z` is a topological group with a measurable structure in which open sets
are measurable, and `Z₀` is a subgroup of `Z`.

- `cosetValues Z₀ F` (definition): only the group structure (the other section instances are
  omitted); `F : Z → E` for any type `E`.
- `cosetValues_mk`: only the group structure, and right `Z₀`-invariance
  `hF : ∀ z, ∀ b ∈ Z₀, F (z * b) = F z` of `F : Z → E`.
- `preimage_mk_singleton`: only the group structure.
- `hasSum_integral_quotient`: the section instances, `[MeasurableMul Z]`,
  `[Countable (Z ⧸ Z₀)]`, a left invariant measure `μ`, `hZ₀ : IsOpen (Z₀ : Set Z)`, a complete
  real normed space `E`, `hF` and `hint : Integrable F μ`.
- `eq_zero_of_integral_inv_character_mul_eq_zero`: the section instances,
  `[MeasurableMul Z]`, commutativity `hcomm : ∀ a b : Z, a * b = b * a`, `[Z₀.Normal]`,
  `[Group.FG (Z ⧸ Z₀)]`, a left invariant measure `μ`, `hZ₀`,
  `hpos : 0 < μ (Z₀ : Set Z)`, `hfin : μ (Z₀ : Set Z) < ∞`, `hF` and `hint` for `F : Z → ℂ`,
  and `h`: `∫_Z χ(z)⁻¹ F(z) dμ(z) = 0` for every `χ : Z →* ℂˣ` with `|χ| = 1` and
  `z ↦ χ(z)` continuous.

**Section `Central`.** `G` is a group with a topology.

- `HasFGCompactOpenQuotients A` (definition): no further hypotheses.

Then `G` is moreover a topological group with a compact open subgroup
(`[Nonempty (CompactOpenSubgroup G)]`); `A` is a subgroup of `G` with a measurable structure
in which open sets are measurable, `μA` a measure on `A`, and `Ξ, σ : G → ℝ`.

- `eq_zero_of_forall_centralProjection_eq_zero`: `[MeasurableMul A]`,
  `[μA.IsMulLeftInvariant]`, `[μA.IsOpenPosMeasure]`, `[IsFiniteMeasureOnCompacts μA]`,
  `hw : CentralWeights μA Ξ σ` (the published hypotheses of `CentralProjection` under which
  `p_χ` converges absolutely on `C(G)`), `hA : IsClosed (A : Set G)`,
  `hAc : A ≤ Subgroup.center G`, `hFG : HasFGCompactOpenQuotients A`,
  `hf : f ∈ schwartzSubmodule Ξ σ` (`f ∈ C(G)`), and `h`: `centralProjection μA χ f = 0` for
  every `χ : A →* ℂˣ` with `|χ| = 1` and `a ↦ χ(a)` continuous.

In Waldspurger's situation `A = A_G` is closed and central, `μA` is a Haar measure on `A_G`
(left invariant, positive on open sets, finite on compacts), `Ξ, σ` are his functions of II.1
and I.1 satisfying `CentralWeights`, and `f = φ`.

## Definitions

- `cosetValues Z₀ F q = F(q̇)`, where `q̇ = Quotient.out q` is the chosen representative of the
  left coset `q ∈ Z / Z₀`. For right `Z₀`-invariant `F` it is the function induced by `F` on
  `Z / Z₀` (`cosetValues_mk`); it is the `f` to which the discrete uniqueness theorem is
  applied.
- `HasFGCompactOpenQuotients A`: for every compact open subgroup `K` of `G` there is a finite
  set `s ⊆ A` with `⟨s⟩ ⊔ (A ∩ K) = A`, where `A ∩ K` is `K.toSubgroup.subgroupOf A`. When
  `A` is central, `A ∩ K` is normal in `A` and this says that `A / (A ∩ K)` is finitely
  generated (shown inside the proof of the main theorem). The condition is stated without the
  quotient group because the group structure on `A / (A ∩ K)` needs the normality instance.

## Results

- `cosetValues_mk`: for right `Z₀`-invariant `F`, `cosetValues Z₀ F (z Z₀) = F(z)`.
- `preimage_mk_singleton`: the coset `{z | z Z₀ = q}` is the left translate `q̇ Z₀`.
- `hasSum_integral_quotient` (**integration over the cosets of an open subgroup**):
  `∑_{q ∈ Z/Z₀} μ(Z₀) cosetValues Z₀ F q` has sum `∫_Z F dμ`.
- `eq_zero_of_integral_inv_character_mul_eq_zero` (**Fourier inversion on `Z`**): under its
  hypotheses, `F = 0`.
- `eq_zero_of_forall_centralProjection_eq_zero` (**Fourier inversion on `A_G`**): if
  `f ∈ C(G)` and `p_χ f = 0` for every continuous unitary character `χ` of `A`, then `f = 0`.
  Contrapositively: if `f ≠ 0`, some `χ ∈ Â_G` has `p_χ f ≠ 0`.

## Proof notes

1. `cosetValues_mk`: for `q = z Z₀`, `q̇⁻¹ z ∈ Z₀` (`QuotientGroup.eq`, `QuotientGroup.out_eq'`), so
   `F(z) = F(q̇ (q̇⁻¹ z)) = F(q̇)`.
2. `hasSum_integral_quotient`: `Z / Z₀` is discrete since `Z₀` is open
   (`QuotientGroup.discreteTopology`), so the cosets `mk⁻¹{q}` are open, hence measurable;
   they are pairwise disjoint and cover `Z`. `hasSum_integral_iUnion` (countable index set)
   gives `∑_q ∫_{q̇ Z₀} F = ∫_Z F`. On `q̇ Z₀` the function `F` is the constant `F(q̇)`
   (step 1), and `μ(q̇ Z₀) = μ(Z₀)` by left invariance (`preimage_mk_singleton`,
   `measure_preimage_mul`).
3. `eq_zero_of_integral_inv_character_mul_eq_zero`: `hcomm` makes `Z / Z₀` a commutative
   group, countable by `countable_of_fg`. Put `f = cosetValues Z₀ F`. Step 2 for `|F|` shows that
   `μ(Z₀) |f|` is summable, hence `|f|` is summable since `0 < μ(Z₀) < ∞`. For a unitary
   character `ψ` of `Z / Z₀`, the character `χ = ψ⁻¹ ∘ mk` of `Z` is unitary and continuous
   (constant on the open cosets), and `z ↦ χ(z)⁻¹ F(z) = ψ(z Z₀) F(z)` is integrable and right
   `Z₀`-invariant; step 2 and `h` give `μ(Z₀) characterSum f ψ = 0`. Hence
   `characterSum f ψ = 0` for every unitary `ψ`, so `f = 0` by
   `eq_zero_of_characterSum_eq_zero`, and `F(z) = f(z Z₀) = 0` by step 1.
4. `eq_zero_of_forall_centralProjection_eq_zero`: `f` lies in a level `C_K` for a compact open
   `K` (`mem_schwartzSubmodule_iff`). Let `A₀ = A ∩ K`. Since `A` is central, `A` is
   commutative and `A₀` is normal. `hFG` gives `A / A₀` finitely generated: the image of
   `⟨s⟩` under `A → A / A₀` is `⟨image of s⟩` (`MonoidHom.map_closure`), and it is everything
   because every `a ∈ ⟨s⟩ ⊔ A₀` is `y z` with `y ∈ ⟨s⟩`, `z ∈ A₀`
   (`Subgroup.mem_sup_of_normal_right`). `A₀` is open in `A` (preimage of `K`), so
   `μA(A₀) > 0`; it is compact (`A` closed, `K` compact), so `μA(A₀) < ∞`. For fixed `g`,
   `F(a) = f(a g)` is integrable on `A` (`CentralWeights.integrable_of_mem_level`) and right
   `A₀`-invariant: for `b ∈ A₀`, `f(a b g) = f(b (a g)) = f(a g)` by centrality and left
   `K`-invariance of `f`. The integral `∫_A χ(a)⁻¹ F(a) dμA(a)` is `(p_χ f)(g)`, which is `0`
   by `h`. Step 3 gives `F = 0`, so `f(g) = F(1) = 0`.

## Relation to the Library

- `CentralProjection` defines `p_χ` and proves its absolute convergence under
  `CentralWeights`; this module uses that integrability for every `g`.
- The other half of the end of the proof of Theorem VIII.1.1 is that `p_χ φ = 0` for each
  `χ ∈ Â_G` (from `ω(ˇφ) = 0` and Theorem VIII.4.2). It is not part of this module, and no
  statement here combines the two halves.

## Open obligations

`HasFGCompactOpenQuotients A_G` for Waldspurger's `A_G` is not proved here. It holds because
`A_G ≅ (F^×)^r` as a topological group and `F^× / U` is finitely generated (`ℤ ×` a finite
group) for every compact open subgroup `U` of `F^×`. The hypotheses `CentralWeights` for
Waldspurger's `Ξ, σ` and the existence of the Haar measure on `A_G` are also inputs.
