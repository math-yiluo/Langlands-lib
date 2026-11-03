# The induced constant term `f ↦ f^{(P),Ind}` and transitivity of constant terms (III.6)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermInd`, namespace
`Langlands.HarishChandraSchwartz`. It builds on
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTerm` (`constantTerm`,
`conjUnipotent`, `ConstantTermData`, `ConstantTermEstimate`, `constantTerm_smul`) and
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations` (`translate`,
`TranslationWeights`) and on the Library module `Langlands.Group.HaarModulus`
(`HaarModulus.normalizerConj`, `HaarModulus.restrictCharacter`,
`HaarModulus.isOpen_ker_restrictCharacter`), the Haar modulus of the conjugation action
of a subgroup normalizing `U`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082.

- III.6 (printed p. 272, PDF p. 38), after the definition of `f^{(P)}`: "On définit un
  homomorphisme `G × G` équivariant `C(G) → I^{G×G}_{P×P} C(M)`, `f ↦ f^{(P),Ind}` par
  `f^{(P),Ind}(g₁, g₂) = (ρ(g₁)λ(g₂)f)^{(P)}` pour tous `g₁, g₂ ∈ G`. Si `P' = M'U'` est
  un sous-groupe parabolique semi-standard contenant `P`, on a comme en I.6 un diagramme
  commutatif" with vertices `C(G)`, `I^{G×G}_{P×P} C(M)`, `I^{G×G}_{P'×P'} C(M')` and
  `I^{G×G}_{P'×P'} I^{M'×M'}_{M'∩P × M'∩P} C(M)`.
- I.6 (printed p. 250, PDF p. 16): the same diagram for `A(G)`. The arrows are
  `α : f ↦ f^{ind}_P`, `β : f ↦ f^{ind}_{P'}`, `δ` deduced by functoriality from
  `f ↦ f^{ind}_{M'∩P}`, and `γ` the isomorphism of I.3.
- I.3 (printed pp. 243–244, PDF pp. 9–10): `I^G_P V` is the space of functions
  `f : G → V`, right invariant under an open subgroup, with
  `f(m u g) = δ_P(m)^{1/2} π(m) f(g)`. For `P ⊂ P'` the isomorphism
  `I^G_P V ≃ I^G_{P'}(I^{M'}_{P∩M'} V)` sends `f` to `g ↦ (m' ↦ δ_{P'}(m')^{-1/2} f(m' g))`.
- I.6 (printed p. 249, PDF p. 15): `ρ` and `λ` are right and left translation of
  functions; the proof of Lemma I.6.1 identifies `λ(g₂⁻¹)ρ(g₁)f` with `g ↦ f(g₂ g g₁)`.
  So `(ρ(g₁)λ(g₂)f)(x) = f(g₂⁻¹ x g₁)`, the published `translate g₁ g₂ f`.

## Scope: abstract data and explicit hypotheses

As in `ConstantTerm`, the reductive group, its parabolic subgroups, the Haar measures on
the unipotent radicals and the modulus characters are not constructed. The module works
with:

- a topological group `G` with its Borel σ-algebra;
- for `P = M U`: subgroups `M`, `U` of `G`, a proof `hMU : M ≤ Subgroup.normalizer U`, a
  measure `ν` on `U` and a character `δ : M →* ℝ≥0ˣ` (Waldspurger's `du` and `δ_P`);
- for `P' = M' U'`: in the same way `M'`, `U'`, `ν'`, `δ'` (and `hMU'`);
- for the parabolic subgroup `P ∩ M' = (M ∩ M')(U ∩ M')` of `M'`: a measure `νi` on
  `U ∩ M'` (`U.subgroupOf M'`) and a character `δi` of `M ∩ M'` (`M.subgroupOf M'`).
  For Waldspurger's data `M ⊂ M'`, so `M ∩ M' = M`.

The following properties of these objects are hypotheses of the general results. For
Waldspurger's data they are standard facts about Haar measures and modulus characters.

- `IsConjModulus hMU ν δ`: for every `m ∈ M`, the image of `ν` under `u ↦ m u m⁻¹` is
  `δ(m)⁻¹ ν`, that is `ν(m S m⁻¹) = δ(m) ν(S)`. This is the relation between `δ_P` and
  the Haar measure of `U`. It is proved here (`isConjModulus_restrictCharacter`) when
  `U` is locally compact, `ν` is a regular Haar measure and `δ` is the Library's Haar
  modulus `HaarModulus.restrictCharacter U M hMU`, whose value at `m` is Mathlib's
  `mulEquivHaarChar` of `u ↦ m u m⁻¹`. If moreover `U` is nonarchimedean and `M` is
  closed, the hypotheses `ConstantTermData ν δ` of `ConstantTerm` are proved
  (`constantTermData_restrictCharacter`). The module does not identify this Haar modulus
  with Waldspurger's algebraic `δ_P(m) = |det Ad(m)|_{Lie U}|`.
- `ν.IsMulLeftInvariant` and `ν.IsMulRightInvariant`: `ν` is invariant under left and
  under right translations of `U`. These two hypotheses alone do not make `ν` a Haar
  measure (the zero measure satisfies them). In Waldspurger's application `ν` must be
  supplied as a Haar measure on `U`, and its right invariance comes from the
  unimodularity of `U`; neither is proved here.
- `TransitivityData ν δ ν' δ' νi δi`, a structure with fields:
  - `le_unipotent : U' ≤ U`;
  - `measure_eq_map`: `ν` is the image of `νi ⊗ ν'` under `unipotentMul`,
    `(v, u') ↦ v u'`. In Waldspurger's application this is the integration formula
    attached to the decomposition `U = (U ∩ M') U'`, and it fixes how the three Haar
    measures are normalized. The field itself is only this equality of measures: it does
    not assert that `unipotentMul` is surjective or injective, nor any algebraic
    decomposition of `U` (with zero measures and trivial characters the structure holds
    for any subgroups with `U' ≤ U`);
  - `delta_mul`: `δ(m) = δ'(m) δi(m)` for `m ∈ M ∩ M'`;
  - `delta_unipotent`: `δ'(v) = 1` for `v ∈ U ∩ M'`.

The induced space `I^{G×G}_{P×P} C(M)` is not defined as a type. The module proves the
properties that put `f^{(P),Ind}` in it: the transformation law under `(P × P)` on the
left, invariance on the right under `H × H` for an open subgroup `H`, and values in
`C(M)`. The isomorphism `γ` of I.3 is also not defined. The diagram is proved pointwise,
with the factor `δ'(m₁)^{-1/2} δ'(m₂)^{-1/2}` of `γ` written out.

## Definitions

- `conjUnipotentHomeomorph hMU m : U ≃ₜ U`: conjugation `u ↦ m u m⁻¹` by `m ∈ M`, with
  inverse conjugation by `m⁻¹`.
- `IsConjModulus hMU ν δ : Prop`: the modulus relation above.
- `constantTermInd ν δ f g : M → ℂ`, for `f : G → ℂ` and `g = (g₁, g₂) ∈ G × G`:
  `f^{(P),Ind}(g₁, g₂) = (ρ(g₁)λ(g₂)f)^{(P)} = constantTerm ν δ (translate g₁ g₂ f)`.
- `unipotentMul hU' : (U ∩ M') × U' → U`, `(v, u') ↦ v u'`, for `hU' : U' ≤ U`.
- `TransitivityData ν δ ν' δ' νi δi : Prop`: the structure above.

## Results

Modulus relation (`G` a topological group with its Borel σ-algebra):

- `IsConjModulus.integral_comp`: `∫_U φ(m u m⁻¹) dν(u) = δ(m)⁻¹ ∫_U φ dν` for every
  `φ : U → ℂ`.
- `ConstantTermData.of_isConjModulus`: if `M` is closed, `IsConjModulus hMU ν δ` holds and
  `δ` is trivial on `M ∩ H` for every compact open subgroup `H`, then
  `ConstantTermData ν δ` holds.
- `isConjModulus_restrictCharacter` (`U` locally compact, `ν` a regular Haar measure on
  `U`): `IsConjModulus hMU ν (HaarModulus.restrictCharacter U M hMU)`.
- `eq_one_of_isOpen_ker_of_isCompact`: a character `χ : M →* ℝ≥0ˣ` with open kernel is
  trivial on every compact subgroup `K` of `M`.
- `constantTermData_restrictCharacter` (`U` locally compact and nonarchimedean, `M`
  closed, `ν` a regular Haar measure on `U`):
  `ConstantTermData ν (HaarModulus.restrictCharacter U M hMU)`.
- `sqrt_mul_sqrt_mul_sqrt_conj`:
  `δ(m₁)^{1/2} δ(m₂)^{1/2} δ(m₂⁻¹ m m₁)^{1/2} = δ(m)^{1/2} δ(m₁)` for any character `δ`.
- `IsConjModulus.constantTerm_translate`: for all `f : G → ℂ` and `m₁, m₂, m ∈ M`,
  `(ρ(m₁)λ(m₂)f)^{(P)}(m) = δ(m₁)^{1/2} δ(m₂)^{1/2} f^{(P)}(m₂⁻¹ m m₁)`.
- `constantTerm_translate_unipotent` (`ν` left and right invariant): for all
  `u₁, u₂ ∈ U`, `(ρ(u₁)λ(u₂)f)^{(P)} = f^{(P)}`.

The induced constant term (the first two need only a measurable structure on `G`):

- `constantTermInd_translate` (`G × G`-equivariance):
  `(ρ(h₁)λ(h₂)f)^{(P),Ind}(g₁, g₂) = f^{(P),Ind}(g₁ h₁, g₂ h₂)`.
- `IsBiInvariant.constantTermInd_mul` (smoothness): if `f` is bi-invariant under a
  subgroup `H`, then `f^{(P),Ind}(g₁ h₁, g₂ h₂) = f^{(P),Ind}(g₁, g₂)` for `h₁, h₂ ∈ H`.
  Every `f ∈ C(G)` is bi-invariant under some compact open subgroup.
- `ConstantTermData.constantTermInd_mem_schwartzSubmodule`: if `G` has a compact open
  subgroup, `ConstantTermData ν δ`, `ConstantTermEstimate ν δ Ξ σ ΞM σM`,
  `TranslationWeights Ξ σ`, `ΞM > 0` and `σM ≥ 0` hold, then
  `f^{(P),Ind}(g₁, g₂) ∈ C(M)` for `f ∈ C(G)`.
- `IsConjModulus.constantTermInd_mul` (the law of `I^{G×G}_{P×P}`; `ν` left and right
  invariant, `IsConjModulus hMU ν δ`): for all `f : G → ℂ`, `m₁, m₂, m ∈ M`,
  `u₁, u₂ ∈ U` and `g₁, g₂ ∈ G`,
  `f^{(P),Ind}(m₁ u₁ g₁, m₂ u₂ g₂)(m) = δ(m₁)^{1/2} δ(m₂)^{1/2} (ρ(m₁)λ(m₂) f^{(P),Ind}(g₁, g₂))(m)`.

Transitivity (`G` moreover second countable; `νi` and `ν'` s-finite;
`hT : TransitivityData ν δ ν' δ' νi δi`):

- `continuous_unipotentMul`: `unipotentMul` is continuous.
- `TransitivityData.constantTerm_constantTerm`: for `m ∈ M ∩ M'` and `f : G → ℂ` such
  that `u ↦ f(m u)` is `ν`-integrable, `(f^{(P')})^{(P∩M')}(m) = f^{(P)}(m)`. Here the
  inner constant term is `constantTerm ν' δ' f : M' → ℂ` and the outer one is taken in
  the group `M'` with `νi`, `δi`.
- `TransitivityData.constantTerm_constantTerm_of_mem`: the same for `f ∈ C(G)`, if `G` has
  a compact open subgroup, `ConstantTermEstimate ν δ Ξ σ ΞM σM`, `Ξ > 0` and `σ ≥ 0` hold.
  The integrability then holds by `integrable_of_mem_schwartzSubmodule`.
- `TransitivityData.constantTermInd_constantTermInd` (the diagram of III.6; moreover
  `IsConjModulus hMU' ν' δ'`): for `g₁, g₂ ∈ G`, `m₁, m₂ ∈ M'`, `m ∈ M ∩ M'` and `f`
  such that `u ↦ (ρ(m₁ g₁)λ(m₂ g₂)f)(m u)` is `ν`-integrable,
  `(f^{(P'),Ind}(g₁, g₂))^{(P∩M'),Ind}(m₁, m₂)(m) = δ'(m₁)^{-1/2} δ'(m₂)^{-1/2} f^{(P),Ind}(m₁ g₁, m₂ g₂)(m)`.
  The left side is `δ(β(f))` evaluated at `(g₁, g₂)`, then `(m₁, m₂)`, then `m`. The
  right side is `γ(α(f))` evaluated at the same points, with `γ` given by the formula
  of I.3 for `G × G`. So the identity is `δ ∘ β = γ ∘ α`.

Not in this module: the linear or continuous structure of `f ↦ f^{(P),Ind}` as a map
into a space `I^{G×G}_{P×P} C(M)`, the identification of `HaarModulus.restrictCharacter`
with Waldspurger's `δ_P`, and the other facts listed above as hypotheses.

## Proof notes

1. `integral_comp`. Conjugation is a homeomorphism (`conjUnipotentHomeomorph`), so
   `integral_map_equiv` turns the integral into one against `ν.map (u ↦ m u m⁻¹)`. That
   measure is `δ(m)⁻¹ ν` by `IsConjModulus`.
   `isConjModulus_restrictCharacter`. Conjugation by `m` on `U` is
   `HaarModulus.normalizerConj U m`, and Mathlib's `mulEquivHaarChar_smul_map` gives
   `c • ν.map α = ν` for its Haar character `c`; multiplying by `c⁻¹` gives the relation.
   The Haar character is computed with the Borel σ-algebra of `U`, and `ν` lives on the
   σ-algebra induced from `G`. These agree because `G` is a Borel space, and the proof
   rewrites one into the other.
   `eq_one_of_isOpen_ker_of_isCompact`. The kernel of `χ` on `K` is an open subgroup of
   the compact group `K`, so it has finite index `n ≠ 0`. Then `χ(m)ⁿ = 1`, and a
   nonnegative real number whose `n`-th power is `1` equals `1`.
   `constantTermData_restrictCharacter`. `M ∩ H` is a compact subgroup of `M` for every
   compact open subgroup `H` of `G` (`CompactOpenSubgroup.subgroupOf` of `ConstantTerm`,
   which uses that `M` is closed). The kernel of `restrictCharacter` is open
   (`HaarModulus.isOpen_ker_restrictCharacter`, which uses that `U` is nonarchimedean).
   So the previous lemma and `ConstantTermData.of_isConjModulus` apply.
2. `constantTerm_translate`. For `u ∈ U`,
   `(ρ(m₁)λ(m₂)f)(m u) = f(m₂⁻¹ m u m₁) = f((m₂⁻¹ m m₁)(m₁⁻¹ u m₁))`. Step 1 for
   conjugation by `m₁⁻¹` gives the factor `δ(m₁)`. The scalar identity
   `sqrt_mul_sqrt_mul_sqrt_conj` matches the square roots of `δ` on both sides. It is
   proved from multiplicativity of `δ` and `√(xy) = √x √y`.
3. `constantTerm_translate_unipotent`. With `a = m⁻¹ u₂⁻¹ m ∈ U`,
   `(ρ(u₁)λ(u₂)f)(m u) = f(m · a u u₁)`. Right invariance of `ν` removes `u₁`, and left
   invariance removes `a`.
4. `constantTermInd_translate` and `IsBiInvariant.constantTermInd_mul` follow from
   `translate_translate` and `IsBiInvariant.translate_eq`.
   `constantTermInd_mem_schwartzSubmodule` combines
   `TranslationWeights.translate_mem_schwartzSubmodule` with
   `ConstantTermData.constantTerm_mem_schwartzSubmodule`.
5. `constantTermInd_mul`. `ρ(m₁ u₁ g₁)λ(m₂ u₂ g₂) = ρ(m₁)λ(m₂) ρ(u₁)λ(u₂) ρ(g₁)λ(g₂)`
   (`translate_translate`). Then steps 2 and 3 apply.
6. `constantTerm_constantTerm`. By `measure_eq_map`, the integral over `U` is an integral
   over `(U ∩ M') × U'` of `φ(v u')`, with `φ(u) = f(m u)`. `φ ∘ unipotentMul` is
   integrable for the product measure (`integrable_map_measure`, using continuity of
   `unipotentMul`). Fubini (`integral_prod`) writes it as `∫_{U∩M'} ∫_{U'} φ(v u')`.
   The double constant term is
   `δi(m)^{1/2} ∫_{U∩M'} δ'(m v)^{1/2} ∫_{U'} f(m v u') dν' dνi`. Here `δ'(m v) = δ'(m)`
   by `delta_unipotent`, and `δ(m)^{1/2} = δ'(m)^{1/2} δi(m)^{1/2}` by `delta_mul`.
   Second countability of `G` passes to the subgroups, which makes the continuous map
   `unipotentMul` measurable for the product σ-algebra.
7. `constantTermInd_constantTermInd`. Step 2 for `P'` gives
   `ρ(m₁)λ(m₂) f^{(P')}_{(g₁,g₂)} = c⁻¹ (ρ(m₁)λ(m₂)ρ(g₁)λ(g₂)f)^{(P')}` with
   `c = δ'(m₁)^{1/2} δ'(m₂)^{1/2} ≠ 0`. Then `constantTerm_smul` and step 6 for
   `ρ(m₁ g₁)λ(m₂ g₂)f` give the identity.
