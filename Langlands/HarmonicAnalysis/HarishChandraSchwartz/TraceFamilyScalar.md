# The scalar of `π[φ]` on irreducible tempered representations (proof of Waldspurger III.7.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceFamilyScalar`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceOrthogonality` (Worker 249):
  `traceOrthogonalityIntegrand`, `traceOrthogonalityIntegrand_mk`,
  `traceCoefficient_smoothContragredient`, `integral_traceOrthogonalityIntegrand_eq_zero`,
  `integral_traceOrthogonalityIntegrand_eq_formalDegree_of_mem`; through its imports
  `formalDegree`, `orthogonalityIntegrand` (`SchurOrthogonality`), `traceCoefficient`,
  `traceFamily`, `traceFamily_operator_eval` (`TraceCoefficientFamily`), the operator
  `IdempotentFamily.operator` and `exists_compactOpenSubgroup_fixed` (`SchwartzActionFamily`),
  `HasTemperedCoefficients`, `ext_smoothDual` (`SchwartzAction`), `L2Weights`,
  `ConvolutionWeights`, `TranslationWeights`, `HasRapidlyDecreasingCoefficientsOn`, the predicate
  `IsSquareIntegrableModCentralSubgroup` (Worker 200, `CentralSubgroupCoefficients`) and
  `Jacquet.compressedAction`;
- `Langlands.Representation.Twist.AdmissibilityProof` (`fixedVectors_twist_eq_of_le_ker`,
  `isAdmissible_twist_iff`) and `Langlands.Representation.Twist.SmoothPartDefinitions`
  (`smoothContragredientTwistEquiv`), with `twist` and `isIrreducible_twist_iff`;
- `Langlands.Topology.ComplexCharacterExtension` (`exists_complex_character_extension`);
- from Mathlib: `AddChar.sum_apply_eq_ite` (orthogonality of the characters of a finite abelian
  group), `MeasurePreserving.setIntegral_preimage_emb`, `MeasurableEmbedding.restrict_map`,
  `integral_map`, `integral_iUnion`, `integral_mul_left_eq_self`,
  `QuotientGroup.quotientKerEquivRange`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The quoted displays carry no overline in the printed text (checked on the
rendered PDF pages 40 and 41).

- Proof of Proposition III.7.1, printed p. 274 (PDF p. 40): "Fixons `(ω, E) ∈ O`. Pour tout
  sous-groupe ouvert compact `H` de `G`, notons `ε_H` et `ψ_H` les fonctions sur `G` définies
  par [...] `ψ_H(g) = trace[ω̌(ε_H) ω̌(g) ω̌(ε_H)]`. Soit `φ ∈ C_c(G/G¹)`. Posons `φ_H = φ ψ_H`.
  [...] On définit un opérateur `π[φ] ∈ End_ℂ V` par `π[φ] v = π(φ_H) v`, où `H` est n'importe
  quel sous-groupe ouvert compact de `G` fixant `v`."
- Same page: "Supposons `π` irréductible et calculons `π[φ]`. Soient `v ∈ V`, `v̌ ∈ V̌` et `H` un
  sous-groupe ouvert compact de `G` fixant `v` et `v̌`. On a les égalités
  `⟨π[φ] v, v̌⟩ = ∫_G φ(g) ψ_H(g) ⟨π(g) v, v̌⟩ dg = ∫_{G¹\G} φ(g) f(g) dg`, où
  `f(g) = ∫_{G¹} ψ_H(xg) ⟨π(xg) v, v̌⟩ dx`. Introduisons les caractères centraux `χ_ω` et `χ_π`
  de `ω` et `π`. Il est clair que `f = 0` si les restrictions de `χ_ω` et `χ_π` à `A_G ∩ G¹` sont
  distinctes. Supposons ces restrictions égales. Posons
  `S = {χ ∈ X(G); χ|_{A_G} = χ_π χ_ω^{-1}}`. Alors `S` est un ensemble fini non vide. Par
  inversion de Fourier sur le groupe abélien fini `G¹A_G \ G`, on a l'égalité
  `f(g) = Σ_{χ ∈ S} χ(g) f_χ`, où
  `f_χ = [G : G¹A_G]^{-1} Σ_{g ∈ G¹A_G\G} f(g) χ^{-1}(g)
  = [G : G¹A_G]^{-1} ∫_{A_G\G} ψ_H(g) ⟨π(g) v, v̌⟩ χ^{-1}(g) dg`."
- Printed p. 275 (PDF p. 41): "D'après III.1 (2), qui se généralise au cas où `π_2` est
  seulement tempérée, cette intégrale est nulle si `π ≄ ω ⊗ χ`. Si `π ≃ ω ⊗ χ`, elle vaut
  `d(π)^{-1} ⟨v, v̌⟩` d'après III.1 (3). Notons qu'alors `d(π) = d(ω)`. Posons alors
  `S(π) = {χ ∈ X(G); π ≃ ω ⊗ χ}`,
  `P_φ(π) = d(ω)^{-1} [G : G¹Z_G]^{-1} Σ_{χ ∈ S(π)} ∫_{G¹\G} φ(g) χ(g) dg`. On obtient
  `⟨π[φ] v, v̌⟩ = P_φ(π) ⟨v, v̌⟩`, i.e. `π[φ]` est l'homothétie de rapport `P_φ(π)`."

## Correspondence and generalizations

- `G¹` and `X(G)`. A surjective homomorphism `p : G →* Λ` onto a commutative group `Λ` with open
  kernel plays the role of `G → G / G¹` (for Waldspurger, `Λ = G / G¹` is a lattice); `X(G)` is
  replaced by the characters `χ : Λ →* ℂˣ` of `Λ`, used on `G` as `χ ∘ p`. The hypothesis `hHN`
  says that every compact open subgroup of `G` lies in `ker p`, as every compact subgroup lies
  in `G¹`.
- `A_G`. A central normal subgroup `A` with `Q = Λ / p(A)` finite (`[Fintype (Λ ⧸ A.map p)]`)
  plays the role of `A_G`; `Q` is the source's finite group `G¹A_G \ G`.
- `φ ∈ C_c(G/G¹)` is a finitely supported `φ : Λ →₀ ℂ`; the function on `G / ker p` given to
  `traceFamily` is `kerLiftFun p φ`. The integral `∫_{G¹\G} φ(g) χ(g) dg` is
  `finsuppCharacterSum φ χ = Σ_λ φ(λ) χ(λ)`, i.e. the measure on `G / G¹` is the counting
  measure.
- Measures. `μ` is a left and right invariant Haar measure on `G` and `ν` a Haar measure on
  `G / A` invariant under inversion (the measure of the Schur orthogonality relations). Their
  relation is the single hypothesis `hcompat`: the image of `μ` restricted to `ker p` under
  `G → G / A` is `m` times `ν` restricted to the image of `ker p`, for a finite `m` (`hm`). In
  Weil's normalization `m` is the measure of `A ∩ ker p`; Waldspurger's measures are fixed in
  I.1. The constant `m |Q|⁻¹` of the Lean results replaces the source's `[G : G¹Z_G]^{-1}`; the
  two are not compared.
- Characters. The central characters `χ_π`, `χ_ω` are explicit `cπ cω : A →* ℂˣ` with
  `π(a) = cπ(a)`, `ω(a) = cω(a)` (`hπc`, `hω`).
- The sum over `S(π)`. `traceFamily_operator_eval_eq_sum` fixes one `χ₀` with
  `χ₀(p(a)) cω(a) = cπ(a)` (an element of the source's `S`) and sums over the characters `η` of
  `Q` (Mathlib's `AddChar (Additive Q) ℂ`), with the condition
  `π ⊗ ((χ₀ η) ∘ p)⁻¹ ≃ ω`, i.e. `π ≃ ω ⊗ (χ₀ η ∘ p)`; the characters `χ₀ η` are exactly the
  source's set `S`. The identification of this sum with a sum over the set `S(π)` itself is not
  stated. The existence of `χ₀` when the central characters agree on `A ∩ ker p` is
  `exists_character_comp_eq` (Waldspurger: "Alors `S` est un ensemble fini non vide").
- The case of distinct central characters on `A ∩ ker p` is
  `traceFamily_operator_eval_eq_zero` (the source's "`f = 0`").
- The formal degree is `formalDegree A hA ν hω hcof hsq hiω` of `SchurOrthogonality` for `ω`
  (the source's `d(ω)`); the source's intermediate `d(π)` and the identity `d(π) = d(ω)` do not
  occur, because the Lean proof transports the integral to `ω` along the equivalence.
- The source's generalization of III.1 (2) to tempered `π_2` enters through the hypothesis
  `hint`: for every character `χ'` of `G` such that `π ⊗ χ'` has central character `cω` on `A`,
  every Schur integrand of `π ⊗ χ'` against `ω` is integrable on `G / A`.
- Derived results, not statements of the paper: `quotientCharacter` and its lemmas,
  `card_mul_eq_sum_addChar`, the measure lemmas of the section `Cosets`, `conj_mk_ker`,
  `kerLiftFun`, `hasCompactSupport_kerLiftFun`, `twist_inv_comp_central`,
  `twistedTraceIntegrand` and its lemmas, `compressedAction_mul_of_smul`,
  `traceCoefficient_mul_of_smul`.

## Scope and hypotheses

`G : Type u` is a group with a topology, `[IsTopologicalGroup G]`. The sections use, as needed:
`[MeasurableSpace G] [BorelSpace G]`, a measure `μ` (`[μ.IsMulLeftInvariant]` for the coset
lemmas); a commutative group `Λ` and `p : G →* Λ`; a subgroup `A` with `[A.Normal]`,
`[MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]` and a measure `ν` on `G ⧸ A`.

The main section `Main` has the variables of `traceFamily`: `[Nonempty (CompactOpenSubgroup G)]`,
weights `Ξ σ : G → ℝ`, `[SecondCountableTopology G]`, `μ` with `[μ.IsHaarMeasure] [SFinite μ]
[μ.IsMulRightInvariant]`, a subgroup `K` with `[CompactSpace K]`; and `p`, `A` with
`hA : A ≤ Subgroup.center G`, `ν` with `[ν.IsHaarMeasure] [ν.IsInvInvariant]`, the cofinality
premise `hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K`,
representations `ω : Representation ℂ G W` (`W : Type v`) and `π : Representation ℂ G V`
(`V : Type w`), characters `cπ cω : A →* ℂˣ` with `hπc` and `hω`.

`traceFamily_operator_eval_eq_sum` and `traceFamily_operator_eq_smul` assume in addition:
`[Fintype (Λ ⧸ A.map p)]`; `hp : Function.Surjective p`; `hN : IsOpen (p.ker : Set G)`;
`hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker`; `m : ℝ≥0∞` with `hm : m ≠ ∞` and
`hcompat`; `hc : ConvolutionWeights μ K Ξ σ`, `ht : TranslationWeights Ξ σ`,
`hw : L2Weights μ Ξ σ`; `hsq : IsSquareIntegrableModCentralSubgroup A hA ω ν` and
`hiω : ω.IsIrreducible`; `hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker
(contragredientRep ω).representation` (the conclusion of Cor. III.1.2 for `ω̌` on `ker p`);
`hπa : IsAdmissible π`, `hiπ : π.IsIrreducible`, `hT : HasTemperedCoefficients Ξ σ π`; `hint`;
`χ₀ : Λ →* ℂˣ` with `hχ₀ : ∀ a : A, χ₀ (p a) * cω a = cπ a`; `φ : Λ →₀ ℂ`. The first also takes
`H : CompactOpenSubgroup G`, `v` with `hv : v ∈ fixedVectors π H.toSubgroup` and
`ℓ : SmoothDual π`; the second takes any `v : V`.

`traceFamily_operator_eval_eq_zero` assumes `hN`, `hHN`, `hc`, `ht`, `hw`,
`hωa : IsAdmissible ω`, `hD`, `hπa`, `hT`, an element `a ∈ A` (`haA`) with `p a = 1` (`hpa`) and
`cπ ⟨a, haA⟩ ≠ cω ⟨a, haA⟩` (`hca`), `φ`, `H`, `v` with `hv`, and `ℓ`; it needs neither
irreducibility, nor square integrability, nor `hcompat`, `hint`, `hp` or finiteness of `Q`.

## Definitions

- `quotientCharacter B η : Λ →* ℂˣ`, for `B : Subgroup Λ` and `η : AddChar (Additive (Λ ⧸ B)) ℂ`,
  `λ ↦ η(λ B)`.
- `kerLiftFun p φ : G ⧸ p.ker → ℂ`, `g ker p ↦ φ(p(g))`.
- `finsuppCharacterSum φ χ = Σ_{λ ∈ supp φ} φ(λ) χ(λ)` (the source's `∫_{G¹\G} φ χ`).
- `twistedTraceIntegrand p A hπc hω hωa H v ℓ χ hχ : G ⧸ A → ℂ`, the function
  `gA ↦ χ(p(g))⁻¹ ψ^{ω̌}_H(g) ℓ(π(g) v)`, defined as the Library's `traceOrthogonalityIntegrand`
  of the twist `π ⊗ (χ ∘ p)⁻¹` against `ω` (central character `cω` by `twist_inv_comp_central`).
- `contragredientRep ω`, the smooth contragredient `ω̌` as a `SmoothRep` (the representation
  whose trace coefficient is the source's `ψ_H`).

## Results

- `quotientCharacter_apply`, `quotientCharacter_of_mem`: its values; it is `1` on `B`.
- `card_mul_eq_sum_addChar`: Fourier inversion on the finite quotient `Q = Λ / B`,
  `|Q| h(q) = Σ_η η(q) Σ_{q'} η(q')⁻¹ h(q')` for every `h : Q → ℂ`.
- `isOpen_preimage_singleton`, `measurableSet_preimage_singleton`: the fibres of `p` are open
  when `ker p` is open.
- `integral_finsupp_comp_mul`: `∫_G φ(p(g)) F(g) dμ = Σ_{λ ∈ supp φ} φ(λ) ∫_{p⁻¹(λ)} F dμ`,
  given integrability of `F` on these fibres.
- `setIntegral_preimage_mul_left`: if `F(a g) = c F(g)` for all `g`, then
  `∫_{p⁻¹(p(a) λ)} F = c ∫_{p⁻¹(λ)} F` (left invariant `μ`).
- `map_mk_restrict_preimage`: `hcompat` transported to every fibre `p⁻¹(p(g))`.
- `measurable_quotientMk`, `setIntegral_preimage_comp_mk`
  (`∫_{p⁻¹(p g)} H(xA) dμ = m ∫_{(p⁻¹(p g))A/A} H dν`), `integrableOn_preimage_comp_mk`, and
  `sum_setIntegral_preimage`: for representatives `r(q)` of the classes `q ∈ Q`,
  `Σ_q ∫_{p⁻¹(r(q))} H(xA) dμ = m ∫_{G/A} H dν` for `H` integrable on `G / A`.
- `conj_mk_ker`, `kerLiftFun_mk`, `hasCompactSupport_kerLiftFun`: the hypotheses of
  `traceFamily` for `kerLiftFun p φ`.
- `twist_inv_comp_central`, `twistedTraceIntegrand_mk` (the formula above),
  `isOpen_ker_inv_comp`, `integrable_twistedTraceIntegrand` (from `hint`).
- `integral_twistedTraceIntegrand`: for `ω` irreducible and square integrable modulo `A`, `π`
  irreducible and admissible, `v` fixed by `H`, `∫_{G/A} twistedTraceIntegrand … χ dν` equals
  `d(ω)⁻¹ ℓ(v)` if `π ⊗ (χ ∘ p)⁻¹ ≃ ω` and `0` otherwise (the evaluation of the source's `f_χ`
  by III.1 (2), (3)).
- `compressedAction_mul_of_smul`, `traceCoefficient_mul_of_smul`: if `ρ(a) = c`, then
  `ψ^ρ_H(g a) = c ψ^ρ_H(g)`.
- `exists_character_comp_eq`: a character `ψ` of `A` trivial on `A ∩ ker p` is `χ₀ ∘ p` on `A`
  for some character `χ₀` of `Λ`.
- `traceFamily_operator_eval_eq_sum` (**the computation of `π[φ]`**): for `v` fixed by `H` and
  `ℓ ∈ SmoothDual π`, `ℓ(π[φ] v) = m |Q|⁻¹ Σ_η c_η ℓ(v)`, where
  `c_η = d(ω)⁻¹ φ̂(χ₀ η)` if `π ⊗ ((χ₀ η) ∘ p)⁻¹ ≃ ω` and `c_η = 0` otherwise, with
  `χ₀ η = χ₀ * quotientCharacter (A.map p) η` and `φ̂ = finsuppCharacterSum φ`.
- `traceFamily_operator_eq_smul` (**`π[φ]` is a homothety**): `π[φ] v = (m |Q|⁻¹ Σ_η c_η) • v`
  for every `v ∈ V`.
- `traceFamily_operator_eval_eq_zero`: if `cπ(a) ≠ cω(a)` for some `a ∈ A ∩ ker p`, then
  `ℓ(π[φ] v) = 0`.

Waldspurger's `P_φ(π)` is the scalar `m |Q|⁻¹ Σ_η c_η`. The polynomiality of `P_φ` on an orbit
`O`, the choice of `φ` with `P_φ|_O = p` and the operator `π(p)` of Proposition III.7.1 itself
are not in this module.

## Proof notes

1. `card_mul_eq_sum_addChar`: swap the sums; `Σ_η η(q) η(q')⁻¹ = Σ_η η(q - q')` is `|Q|` or `0`
   by `AddChar.sum_apply_eq_ite`.
2. `integral_finsupp_comp_mul`: `φ(p(g)) F(g)` is the finite sum over `supp φ` of the
   indicators of the fibres times `φ(λ) F`; `integral_finsetSum`, `integral_indicator`.
3. `map_mk_restrict_preimage`: `μ|_{p⁻¹(p g)}` is the image of `μ|_{ker p}` under `x ↦ g x`
   (left invariance, `MeasurableEmbedding.restrict_map`); the quotient map intertwines it with
   left translation by `gA` on `G / A`, under which `ν` is invariant.
4. `sum_setIntegral_preimage`: the sets `(p⁻¹(r(q)))A / A`, `q ∈ Q`, are open, pairwise
   disjoint and cover `G / A`; each fibre integral is `m` times the integral over its set
   (`setIntegral_preimage_comp_mk`), and `integral_iUnion` sums them.
5. `integral_twistedTraceIntegrand`: if `e : π ⊗ (χ ∘ p)⁻¹ ≃ ω`, the integrand equals the trace
   integrand of `ω` at `e v` and `ℓ ∘ e⁻¹` (`contragredientMap`), and
   `integral_traceOrthogonalityIntegrand_eq_formalDegree_of_mem` gives `d(ω)⁻¹ ℓ(v)` (`e v` is
   fixed by `H` because `H ≤ ker p` and `fixedVectors_twist_eq_of_le_ker`); otherwise
   `integral_traceOrthogonalityIntegrand_eq_zero` applies to the irreducible admissible twist.
6. `traceFamily_operator_eval_eq_sum`: `traceFamily_operator_eval` and
   `traceCoefficient_smoothContragredient` write `ℓ(π[φ] v)` as
   `∫ φ(p(g)) χ₀(p(g)) H₀(gA) dμ` with `H₀` the twisted trace integrand for `χ₀`. Step 2 gives
   `Σ_λ φ(λ) χ₀(λ) h(λ)` with `h(λ) = ∫_{p⁻¹(λ)} H₀(xA) dμ`. `h` is invariant under `p(A)`
   (`setIntegral_preimage_mul_left` with `c = 1`), hence a function on `Q`; step 1 expands it,
   and its Fourier coefficients are `Σ_q η(q)⁻¹ h(r(q)) = m ∫_{G/A} (twisted integrand for
   χ₀ η) dν` (step 4, since on `p⁻¹(r(q))` the two integrands differ by the constant
   `η(q)⁻¹`). Step 5 evaluates these integrals; the rest is rearranging finite sums.
7. `traceFamily_operator_eq_smul`: choose `H` fixing `v` and use `ext_smoothDual`.
8. `traceFamily_operator_eval_eq_zero`: with `I(g)` the integrand of `traceFamily_operator_eval`,
   `I(a g) = cπ(a) cω(a)⁻¹ I(g)` (`traceCoefficient_mul_of_smul` for `ω(a⁻¹) = cω(a)⁻¹`,
   `p(a) = 1`, `π(a) = cπ(a)`), so `∫ I = cπ(a) cω(a)⁻¹ ∫ I` by `integral_mul_left_eq_self`,
   and `∫ I = 0`.
9. `exists_character_comp_eq`: `ψ` factors through `A / (A ∩ ker p) ≃ p(A)`
   (`QuotientGroup.lift`, `quotientKerEquivRange`) and extends to `Λ` by
   `exists_complex_character_extension`.
