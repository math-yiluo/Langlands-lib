# Vanishing of `p_χ φ` (Waldspurger, end of the proof of Theorem VIII.1.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjectionVanishing`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `DiscreteCoefficientSpace`: `subrepresentationCoefficientSpace` (the span `Σ_S A(S)` of the
  coefficient spaces of the subrepresentations `S` satisfying a predicate `p`) and the
  inclusion `ScalarSubReduction.inclusion` of a subrepresentation;
- `KernelQuotient`: `integral_centralProjection_mul_conj` (the Weil formula for the pairing of
  `p_χ φ` with a `χ`-covariant function); through it `CentralProjection`
  (`centralProjection`, `centralProjection_mul_left`, `IsUnitaryCharacter`,
  `IsBiInvariant.centralProjection`) and the published `Langlands.Group.LeftQuotient`
  (`LeftQuotient`, `descend`), `Langlands.Analysis.Local.QuotientMeasure` (`IsCompatible`) and
  `Langlands.Analysis.Local.QuotientWeilKernel` (`orbitKernel`, `orbitKernel_comp`), read in
  namespace `Langlands.QuotientIntegration`;
- `SchwartzAction`: `schwartzAction` (Waldspurger's `π(f)`, III.7), `schwartzAction_eval`,
  `integrable_coefficient`, `HasTemperedCoefficients`, `CompactOpenSubgroup.cofinal`; through
  it `TestFunctions` (`IsBiInvariant.isLocallyConstant`), `L2` (`pairing`, `L2Weights`,
  `Space.check`) and `Basic` (`Space`, `mem_schwartzSubmodule_iff`, `Space.coe_mem`);
- transitively, `Langlands.Representation.Unitary.Basic` (`InvariantPositiveForm`,
  `InvariantPositiveForm.comap`) and `Langlands.Representation.Unitary.HermitianDual`
  (`toSmoothDual`, `smoothDualEquiv`, `rightFunctional`);
- `Langlands.Analysis.Local.QuotientMass`: `IsCompatible.isOpenPosMeasure` (a compatible
  quotient measure charges every nonempty open set).

From Mathlib it uses `TensorProduct.inductionOn`, `MeasureTheory.integral_inv_eq_self`,
`MeasureTheory.Integrable.comp_inv`, `MeasureTheory.Measure.ae_integrable_of_integrable_comp`,
`MeasureTheory.Integrable.integral_comp`, `MeasureTheory.integral_map`,
`MeasureTheory.integral_eq_zero_iff_of_nonneg`, `Continuous.ae_eq_iff_eq` and
`integral_complex_ofReal`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234. Bars checked on the page image of printed p. 332 (text extraction drops them).

End of VIII.5, printed p. 332 (PDF p. 98): "Démontrons maintenant le Théorème VIII.1.1. Soit
`f ∈ C(G)`. [...] Posons `φ = f − κ(ψ)`. On va montrer que `φ = 0`. Il est clair que
`φ ∈ °C(G)`. De plus `ψ_φ[O, G] = 0` pour tout `O ∈ Θ_G` (Théorème VII.2.5). Donc
`φ̂(ω, G) = 0` pour tout `ω ∈ E₂(G)`, i.e. `ω(ˇφ) = 0` pour tout `ω ∈ E₂(G)`. Supposons
`φ ≠ 0`. Par inversion de Fourier sur le groupe `A_G`, il existe `χ ∈ Â_G` tel que
`p_χ φ ≠ 0`. D'après le Théorème VIII.4.2, on peut alors trouver

- `(ω, E) ∈ E₂(G)_χ`, l'espace `E` étant muni d'un produit hermitien défini positif invariant
  par `G`;
- `v₁, v₂ ∈ E`,

de sorte que l'intégrale `∫_{A_G\G} conj((v₁, ω(g) v₂)) p_χ φ(g) dg` soit non nulle. Mais cette
intégrale est égale à `∫_G conj((v₁, ω(g) v₂)) φ(g) dg`, où encore à
`∫_G (v₂, ω(g) v₁) φ(g⁻¹) dg`, i.e. à `(v₂, ω(ˇφ) v₁)`. Or `ω(ˇφ) = 0`. Contradiction qui
démontre le Théorème VIII.1.1."

On the page image the first two integrands carry a bar over `(v₁, ω(g) v₂)` and the third
carries none. The step from the second to the third integral uses
`conj((v₁, ω(g) v₂)) = (v₂, ω(g⁻¹) v₁)` and `g ↦ g⁻¹`, and the last step pulls `∫_G φ(g⁻¹)`
into the second argument; so Waldspurger's hermitian products are linear in the second
argument and conjugate linear in the first, as is `InvariantPositiveForm.inner` (an
`InnerProductSpace.Core ℂ V`).

Other notation used here:

- `p_χ` (VIII.4, printed p. 327, PDF p. 93): `(p_χ f)(g) = ∫_{A_G} χ⁻¹(a) f(ag) da` for
  `χ ∈ Â_G`, the unitary characters of `A_G`; this is `centralProjection μA χ f g`.
- `π(f)` (III.7, printed p. 273, PDF p. 39): for `(π, V)` admissible tempered, `v ∈ V`,
  `f ∈ C(G)`, `π(f) v` is the unique element with `⟨π(f) v, ˇv⟩ = ∫_G f(g) ⟨π(g) v, ˇv⟩ dg` for
  every `ˇv`; this is `schwartzAction hw hρ hT f v`.
- `ˇf(g) = f(g⁻¹)` (VII.1, printed p. 313, PDF p. 79); for `f ∈ C(G)` this is
  `Space.check hΞ hσ f`.
- `(f₁, f₂)_G = ∫_G conj(f₁(g)) f₂(g) dg` is `pairing μ f₁ f₂` (`L2`).

## What is proved, and the route

Waldspurger argues by contradiction: Theorem VIII.4.2 supplies a coefficient of some
`ω ∈ E₂(G)_χ` whose pairing with `p_χ φ` over `A_G \ G` is nonzero, and the displayed
computation shows that pairing is `(v₂, ω(ˇφ) v₁) = 0`. The module proves the same computation
for abstract data and uses it directly: if `p_χ φ` is itself a finite sum of coefficients of
subrepresentations `S` with `π_S(ˇφ) = 0` (the inclusion `p_χ(°C(G)) ⊂ A₂(G)_χ` of Theorem
VIII.4.2), then the displayed computation applied to each coefficient gives
`(p_χ φ, φ)_G = 0`, the Weil formula turns this into `∫_{A\G} |p_χ φ|² dν = 0`, and continuity
of `p_χ φ` gives `p_χ φ = 0`. This replaces the choice of a single coefficient with nonzero
pairing (which in Waldspurger's argument comes from the positivity of
`(p_χ φ, p_χ φ)_{A_G\G}`) by the positivity itself.

The quotient `A_G \ G` is `LeftQuotient A` with a measure `ν`, and `q̇ = Quotient.out q`. The
module does not construct `°C(G)`, `κ`, `ψ_f`, `E₂(G)_χ` or `A₂(G)_χ`, and does not prove
`ω(ˇφ) = 0` (Theorem VII.2.5), Fourier inversion on `A_G`, or Theorem VIII.4.2; see Open
obligations.

## Scope: abstract data and explicit hypotheses

**Section `Annihilator`.** `G` is a type with a measurable structure, `μ` a measure on `G` and
`φ : G → ℂ`.

- `pairingAnnihilator` (definition), `mem_pairingAnnihilator`: no further hypotheses.

**Section `FormCoefficient`.** `G` is a topological group with a measurable structure in which
open sets are measurable and which has a compact open subgroup
(`[Nonempty (CompactOpenSubgroup G)]`); `μ` is a measure on `G`; `Ξ, σ : G → ℝ`; `V` is a
complex vector space, `ρ : Representation ℂ G V`, and `b : InvariantPositiveForm ρ` is a
`G`-invariant positive definite hermitian form on `V`. Each result also has these section
instances unless stated otherwise.

- `conj_inner_apply`: only the group structure of `G` and `b` (all other section instances are
  omitted).
- `integrable_conj_inner_mul`: `[MeasurableInv G]`, `[μ.IsInvInvariant]`,
  `hw : L2Weights μ Ξ σ`, `hρ : IsSmooth ρ`, `hT : HasTemperedCoefficients Ξ σ ρ`,
  `hΞ : ∀ g, Ξ g⁻¹ = Ξ g`, `hσ : ∀ g, σ g⁻¹ = σ g`, `b`, and `φ : Space Ξ σ` (an element of
  `C(G)` for the weights `Ξ, σ`).
- `integral_conj_inner_mul`: `[MeasurableMul G]`, `[MeasurableInv G]`,
  `[μ.IsMulLeftInvariant]`, `[μ.IsInvInvariant]`, `hw`, `hρ : IsAdmissible ρ`, `hT`, `hΞ`,
  `hσ`, `b`, `φ : Space Ξ σ`.
- `coefficient_mem_pairingAnnihilator`: the instances of `integral_conj_inner_mul`, `hw`,
  `hρ : IsAdmissible ρ`, `hT`, `hΞ`, `hσ`, `b`, `φ : Space Ξ σ` and
  `hφ : schwartzAction hw hρ hT (Space.check hΞ hσ φ) = 0` (`π(ˇφ) = 0`).
- `subrepresentationCoefficientSpace_le`: the instances of `integral_conj_inner_mul`, `hw`,
  `hΞ`, `hσ`, `b`, `hs : IsSmooth ρ`, a predicate `p` on subrepresentations of `ρ`,
  `φ : Space Ξ σ`, and
  `hS : ∀ S, p S → ∃ (hSa : IsAdmissible S.toRepresentation)
  (hT : HasTemperedCoefficients Ξ σ S.toRepresentation),
  schwartzAction hw hSa hT (Space.check hΞ hσ φ) = 0`
  (every `S` with `p S` is admissible with tempered coefficients and `π_S(ˇφ) = 0`).

**Section `Quotient`.** The setting of the Weil formula of `KernelQuotient`: `G` is a
Hausdorff, locally compact, second countable topological group with its Borel structure;
`μG` is finite on compacts; `A` is a subgroup with `hA : IsClosed (A : Set G)` and its Borel
structure; `μA` is s-finite, right invariant and finite on compacts; `LeftQuotient A` (the
cosets `A g`) carries its Borel structure and a measure `ν`; `χ : A →* ℂˣ`.

- `integrable_integral_out`: `hA`, `[MeasurableMul A]`,
  `hν : IsCompatible A μG μA ν` (`ν` nonzero, regular, right invariant, and the Weil formula
  for compactly supported continuous functions), and `hF : Integrable F μG`.
- `integral_conj_mul_mul_left`: only the group structure of `G`, the measurable structure of
  `A` and `μA` (all other section instances are omitted),
  `hχ : IsUnitaryCharacter χ` (`|χ| = 1` and `χ` measurable), and
  `hK : ∀ (a : A) (g : G), K ((a : G) * g) = χ a * K g`.
- `integrable_centralProjection_mul_conj`: `hA`, `[MeasurableMul A]`, `hν`, `hχ`, `hK`, and
  `hint : Integrable (fun g => conj (K g) * φ g) μG`.
- `centralProjection_eq_zero_of_mem_pairingAnnihilator`: `hA`, `[MeasurableMul A]`, `hν`,
  `hχ`, `hcont : Continuous (centralProjection μA χ φ)` and
  `hmem : centralProjection μA χ φ ∈ pairingAnnihilator μG φ`.
- `centralProjection_eq_zero_of_schwartzAction_eq_zero`: `hA`, `[MeasurableMul A]`,
  `[Nonempty (CompactOpenSubgroup G)]`, `[μG.IsMulLeftInvariant]`, `[μG.IsInvInvariant]`,
  `hAc : A ≤ Subgroup.center G`, `hν`, `hχ`, `hw : L2Weights μG Ξ σ`, `hΞ`, `hσ`, a complex
  vector space `V` with `ρ : Representation ℂ G V`, `b : InvariantPositiveForm ρ`,
  `hs : IsSmooth ρ`, a predicate `p`, `φ : Space Ξ σ`, `hS` as in
  `subrepresentationCoefficientSpace_le`, and
  `hmem : ∃ c ∈ subrepresentationCoefficientSpace hs p, ⇑c = centralProjection μA χ φ`
  (`p_χ φ ∈ Σ_S A(S)`).

In Waldspurger's situation `A = A_G` is central and closed, `μG` and `μA` are Haar measures
(`G` is unimodular), `ν` is the quotient measure, `χ ∈ Â_G`, `Ξ` and `σ` are his functions of
II.1 and I.1, `φ ∈ °C(G)`, and `p` is "irreducible, square integrable modulo `A_G`, with
central character `χ`". The hypothesis `hS` is then his `ω(ˇφ) = 0` for `ω ∈ E₂(G)_χ`
together with admissibility and tempered coefficients of those `ω`, and `hmem` is his
inclusion `p_χ(°C(G)) ⊂ A₂(G)_χ` for the representation `ρ` whose subrepresentations
realize the relevant `ω`.

## Definitions

- `pairingAnnihilator μ φ`: the submodule of functions `c : G → ℂ` such that
  `g ↦ conj(c(g)) φ(g)` is `μ`-integrable and `(c, φ)_G = ∫_G conj(c(g)) φ(g) dμ(g) = 0`.
  Integrability is part of the condition because `pairing` is a Bochner integral, which is `0`
  for non-integrable integrands.

## Results

- `mem_pairingAnnihilator`: the membership condition, by definition.
- `conj_inner_apply`: `conj(b(e, ρ(g) v)) = b(v, ρ(g⁻¹) e)`.
- `integrable_conj_inner_mul`: `g ↦ conj(b(e, ρ(g) v)) φ(g)` is `μ`-integrable.
- `integral_conj_inner_mul` (**the displayed computation**):
  `∫_G conj(b(e, ρ(g) v)) φ(g) dμ(g) = b(v, π(ˇφ) e)`; with `e = v₁`, `v = v₂` this is
  Waldspurger's `∫_G conj((v₁, ω(g) v₂)) φ(g) dg = (v₂, ω(ˇφ) v₁)`.
- `coefficient_mem_pairingAnnihilator`: if `π(ˇφ) = 0`, every coefficient
  `g ↦ ℓ(ρ(g) v)` (`v ∈ V`, `ℓ` a smooth functional) lies in `pairingAnnihilator μ φ`.
- `subrepresentationCoefficientSpace_le`: under `hS`, every function of `Σ_S A(S)` (the image
  of `subrepresentationCoefficientSpace hs p` in `G → ℂ`) lies in `pairingAnnihilator μ φ`.
- `integrable_integral_out` (integrability in the Weil formula): for `F` integrable on `G`,
  `q ↦ ∫_A F(a q̇) dμA(a)` is `ν`-integrable on `A \ G`.
- `integral_conj_mul_mul_left`: for `χ`-covariant `K`,
  `∫_A conj(K(a g)) φ(a g) dμA(a) = (p_χ φ)(g) conj(K(g))`.
- `integrable_centralProjection_mul_conj`: for `χ`-covariant `K` with
  `conj(K) φ` integrable on `G`, `q ↦ (p_χ φ)(q̇) conj(K(q̇))` is `ν`-integrable.
- `centralProjection_eq_zero_of_mem_pairingAnnihilator`: if `p_χ φ` is continuous and lies in
  `pairingAnnihilator μG φ`, then `p_χ φ = 0`.
- `centralProjection_eq_zero_of_schwartzAction_eq_zero` (**end of the proof of Theorem
  VIII.1.1**, abstract form): under `hS` and `hmem`, `p_χ φ = 0`.

## Proof notes

1. `conj_inner_apply`: hermitian symmetry gives `conj(b(e, ρ(g) v)) = b(ρ(g) v, e)`, and
   invariance under `g⁻¹` gives `b(ρ(g) v, e) = b(v, ρ(g⁻¹) e)`.
2. `integrable_conj_inner_mul`: `integrable_coefficient` for `ˇφ ∈ C(G)` (`Space.check`), the
   vector `e` and the smooth functional `b(v, ·)` (`toSmoothDual`) makes
   `g ↦ φ(g⁻¹) b(v, ρ(g) e)` integrable; composing with inversion (`Integrable.comp_inv`,
   using inversion invariance of `μ`) and step 1 gives the claim.
3. `integral_conj_inner_mul`: `schwartzAction_eval` for `ˇφ`, `e` and `b(v, ·)` gives
   `b(v, π(ˇφ) e) = ∫_G φ(g⁻¹) b(v, ρ(g) e) dμ(g)`; the substitution `g ↦ g⁻¹`
   (`integral_inv_eq_self`) and step 1 turn this into the left side. These are Waldspurger's
   second and third integrals and his final identification.
4. `coefficient_mem_pairingAnnihilator`: for admissible `ρ`, every smooth functional is
   `b(e, ·)` for some `e ∈ V` (`smoothDualEquiv`, with compact open subgroups cofinal among
   open subgroups); then steps 2 and 3 and `π(ˇφ) = 0`.
5. `subrepresentationCoefficientSpace_le`: for each `S` with `p S`, `b` restricts to an
   invariant positive form on `S` (`InvariantPositiveForm.comap` along the inclusion of `S`);
   the range of the coefficient map of `S` is spanned by the coefficients of pure tensors
   `w ⊗ ℓ` (`TensorProduct.inductionOn`), which lie in the annihilator by step 4; the
   annihilator is a submodule, so it contains the supremum over `S`.
6. `integrable_integral_out`: `orbitKernel_comp` writes `μG` as `ν` composed with the orbit
   kernel `q ↦ (a ↦ a q̇)_* μA`; integrability of `F` against the composition gives
   integrability of `q ↦ ∫ F d(orbit kernel at q)` (`Integrable.integral_comp`), and
   `integral_map` identifies that integral with `∫_A F(a q̇) dμA(a)`.
7. `integral_conj_mul_mul_left`: `conj(K(a g)) = conj(χ(a)) conj(K(g))` and
   `conj(χ(a)) = χ(a)⁻¹` since `|χ(a)| = 1`; then `integral_mul_const`.
8. `integrable_centralProjection_mul_conj`: step 6 for `F = conj(K) φ`, rewritten by step 7.
9. `centralProjection_eq_zero_of_mem_pairingAnnihilator`: `P = p_χ φ` is `χ`-covariant
   (`centralProjection_mul_left`), so `|P|²` descends to a continuous function `F` on `A \ G`
   (`descend`), integrable by step 8 with `K = P`. `integral_centralProjection_mul_conj` of
   `KernelQuotient` with `K = P` gives `∫_{A\G} |P(q̇)|² dν(q) = ∫_G conj(P) φ dμG = 0` (the
   second equality is `hmem`). Hence `F = 0` `ν`-almost everywhere
   (`integral_eq_zero_iff_of_nonneg`), and, since `ν` charges nonempty open sets
   (`IsCompatible.isOpenPosMeasure`) and `F` is continuous, `F = 0` (`Continuous.ae_eq_iff_eq`);
   so `P = 0`.
10. `centralProjection_eq_zero_of_schwartzAction_eq_zero`: by step 5, `p_χ φ = c` lies in
    `pairingAnnihilator μG φ`. Since `φ ∈ C(G)` is bi-invariant under some compact open
    subgroup (`mem_schwartzSubmodule_iff`), so is `p_χ φ` (`IsBiInvariant.centralProjection`,
    using `hAc`), hence `p_χ φ` is locally constant and continuous. Step 9 concludes.

## Relation to the Library

- `DiscreteCoefficientSpace` proves the abstract inclusion of Theorem VIII.4.2: coefficients
  of a semisimple smooth representation lie in `subrepresentationCoefficientSpace` for the
  irreducible subrepresentations; `CentralCoefficientFormula` proves the reproducing identity
  `f(g) = mes(H)⁻¹ (p_χ °e, ρ(g) f)_{A_G\G}` for `f = p_χ φ`, which exhibits `f` as a
  coefficient of the right translation action on `V = p_χ(°C(H \ G))`. Together with the open
  inputs listed there, they are the route to `hmem`.
- `integral_centralProjection_mul_conj` of `KernelQuotient` is the Weil-formula step from
  `A_G \ G` to `G` (first to second integral in the display); `integrable_integral_out` adds
  the integrability of the inner integral that this step leaves implicit.
- `SchwartzAction` defines `π(f)` and its defining property; `L2` defines `pairing` and
  `Space.check`.

## Open obligations

The following inputs of Waldspurger's proof of Theorem VIII.1.1 are not proved here: the
construction of `ψ` (Remark VIII.1.3(ii)) and of `κ`, and `ω(ˇφ) = 0` for all `ω ∈ E₂(G)` for
`φ = f − κ(ψ)` (from Theorem VII.2.5);
admissibility and tempered coefficients of each `ω ∈ E₂(G)_χ`, which `hS` requires; Theorem
VIII.4.2 in Waldspurger's setting, which gives `hmem`; and Fourier inversion on `A_G` (if
`p_χ φ = 0` for every `χ ∈ Â_G` then `φ = 0`), which turns the conclusion
`p_χ φ = 0` for all `χ` into `φ = 0`.
