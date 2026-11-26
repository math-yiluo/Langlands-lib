# Normalized ordinary and twisted parabolic constant terms

Module `Langlands.BaseChange.NormalizedParabolicConstantTerm`.

Let `E` be a nonarchimedean local field (`[Field E] [ValuativeRel E] [TopologicalSpace E]
[IsNonarchimedeanLocalField E]`, any characteristic), `n` a natural number,
`B : GeneralLinear.BlockShape n` a standard block shape, `G = GL_n(E)`,
`P = B.parabolic E` the standard upper block parabolic, `M = B.Levi E` the actual product
Levi, `U = B.unipotentRadical E` its unipotent radical (a subgroup of `P`), and
`K = GL_n(𝒪_E)`. For a continuous automorphism `θ` of `G` the module constructs the
complex-linear map

`φ ↦ φ_{P,θ}`, `φ_{P,θ}(m) = δ_P(m)^{1/2} ∫_U ∫_K φ(k⁻¹ m u θ(k)) dk du`,

from `SchwartzBruhat G` to `SchwartzBruhat M`, with

- `m` included in `G` by the actual block diagonal embedding `B.leviEmbedding E`, which is
  the value of `B.leviInParabolic E` (the embedding used with `B.leviProjection E` in
  `Langlands.Representation.Parabolic.LeviBridges`);
- `u` in `U`, included in `G` through `P`;
- `dk` the Haar probability measure on `K` and `du` the Haar measure on `U` giving
  `U ∩ K` volume one;
- `δ_P^{1/2}` the positive half modulus `LocalFieldData.leviHalfModulus` of the Library,
  taken at `LocalFieldData.ofInstances E` (the data whose topology, valuation and local
  field structure are the instances of `E`). It is the positive square root of
  `LocalFieldData.leviModulus`, `m ↦ ∏_{i<j} |det m_i|^{n_j} / |det m_j|^{n_i}`.

The ordinary constant term is the case `θ = 1`, the twisted one the case
`θ = entrywiseAut σ n` (`k ↦ k^σ`, `σ` applied to every entry). Both are the same
construction with the same half modulus.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle* (2011), II.4.5, printed p. 86 (PDF p. 94): with the Haar
  measures of `G(E)`, `M(E)`, `U(E)` giving `K_E`, `M(𝒪_E)`, `U(𝒪_E) = U(E) ∩ K_E` volume
  one and `dk_E` the restriction to `K_E` of the Haar measure of `G(E)` (so the Haar
  probability on `K_E`), the linear map `C_c^∞(G(E)) → C_c^∞(M(E))` is
  `φ_{P,σ}(m) = δ_{P(E)}(m)^{1/2} ∫_{U(E) × K_E} φ(k⁻¹ m u k^σ) du_E dk_E`, where
  `δ_{P(E)}` is the modulus of `P(E)`, `dμ(p δ p⁻¹) = δ_{P(E)}(p) dμ(δ)`.
- Laumon, *Cohomology of Drinfeld Modular Varieties, Part I* (1996), (4.4.7), printed p. 97
  (PDF p. 59): the `(σ, K_{P,r})`-invariant constant term
  `f_r^{(P)}(m_r) = δ_{P(F_r)}(m_r)^{1/2} ∫_{N(F_r)} ∫_{K_{P,r}} f_r(k⁻¹ m_r n_r σ(k)) dk dn`,
  with `vol(K_{P,r}) = 1` and `vol(N(F_r) ∩ K_{P,r}) = 1`, for an unramified extension.

The module follows these definitions with `k^σ = entrywiseAut σ n k` (the forward
automorphism, not its inverse), the outer integral over `U` and the inner one over `K` as
in Laumon (4.4.7); the evaluation theorems below also give the other order and the
product integral of Henniart–Lemaire. Nothing is assumed about the extension: no
unramifiedness, finiteness or cyclicity, and `K` need not be `σ`-stable for the
definition. The rank `n` is arbitrary (positivity is not needed, since
`Langlands.GeneralLinearGroup.integralSubgroup` is defined in every rank), and the
universe of `E` is free.

## Main definitions

- `standardMaximalCompact E n`: `K = GL_n(𝒪_E)`, the Library subgroup
  `Langlands.GeneralLinearGroup.integralSubgroup (Fin n) (ValuativeRel.valuation E).integer`
  of invertible matrices whose entries and whose inverse's entries are integral. It is open
  (`isOpen_standardMaximalCompact`) and compact (`isCompact_standardMaximalCompact`); the
  instance `compactSpace_standardMaximalCompact` records the latter.
- `standardCompactHaar E n`: the Haar probability measure `Measure.haarMeasure ⊤` on `K`,
  for any Borel measurable structure on `K` (`[MeasurableSpace K] [BorelSpace K]`).
  Instances: `IsHaarMeasure`, `IsProbabilityMeasure`; `standardCompactHaar_univ`.
- `radicalCompact E B`: `U ∩ K = {u | u ∈ K}` as a compact subset of `U` with nonempty
  interior (`TopologicalSpace.PositiveCompacts`); it is compact because `U → G` is a closed
  embedding (`ParabolicConstantTerm.isClosedEmbedding_radicalVal`) and open because `K` is.
- `standardRadicalHaar E B`: the Haar measure `Measure.haarMeasure (radicalCompact E B)` on
  `U`, for any Borel measurable structure on `U`. Instances: `IsHaarMeasure`, `SigmaFinite`;
  `standardRadicalHaar_radicalCompact` states that `U ∩ K` has volume one.
- `normalizedAutParabolicConstantTerm E B θ hθ`, for `θ : GL_n(E) ≃* GL_n(E)` and
  `hθ : Continuous θ`: the normalized `θ`-twisted constant term,
  `SchwartzBruhat (GeneralLinear n E) →ₗ[ℂ] SchwartzBruhat (B.Levi E)`.
- `normalizedParabolicConstantTerm E B`: the case `θ = MulEquiv.refl _` (definitionally,
  `normalizedParabolicConstantTerm_eq`).
- `normalizedTwistedParabolicConstantTerm E B σ`, for a field `F` with a topology,
  `[Algebra F E] [IsModuleTopology F E]` and `σ : E ≃ₐ[F] E`: the case
  `θ = entrywiseAut σ n`, whose continuity is `continuous_entrywiseAut`
  (`Langlands.BaseChange.CyclicAlgebraTopology`), i.e. continuity of the `F`-linear `σ` for
  the `F`-module topology of `E` (`normalizedTwistedParabolicConstantTerm_eq`).
- `parabolicConstantTermOfCompact E B K hK μK μU θ hθ`: the same construction for an
  arbitrary compact subgroup `K` of `GL_n(E)` and arbitrary measures `μK` on `K` and `μU`
  on `U` that are finite on compact sets (with `OpensMeasurableSpace`); the normalized maps
  above are this map at the standard `K` and measures
  (`normalizedAutParabolicConstantTerm_eq`).

## Main theorems

Evaluation, for `φ : SchwartzBruhat (GeneralLinear n E)` and `m : B.Levi E`, writing
`δ m` for `((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ)`:

- `normalizedAutParabolicConstantTerm_apply`: the value at `m` is
  `δ m * ∫ u, ∫ k, φ ((k : G)⁻¹ * B.leviEmbedding E m * ((u : P) : G) * θ k)`
  `∂(standardCompactHaar E n) ∂(standardRadicalHaar E B)`.
- `normalizedAutParabolicConstantTerm_apply_swap`: the same with the compact integral
  outside, `δ m * ∫ k, ∫ u, … ∂(standardRadicalHaar E B) ∂(standardCompactHaar E n)`.
- `normalizedAutParabolicConstantTerm_apply_prod`: the same as a product integral,
  `δ m * ∫ p : U × K, φ ((p.2 : G)⁻¹ * B.leviEmbedding E m * ((p.1 : P) : G) * θ p.2)`
  `∂((standardRadicalHaar E B).prod (standardCompactHaar E n))`.
- `normalizedAutParabolicConstantTerm_apply_of_isHaarMeasure`: the formula of
  `normalizedAutParabolicConstantTerm_apply` holds for every Haar probability measure `μK`
  on `K` and every Haar measure `μU` on `U` with `μU (U ∩ K) = 1`. This rests on
  `eq_standardCompactHaar` (every left-invariant probability measure on `K` is
  `standardCompactHaar E n`) and `eq_standardRadicalHaar` (every Haar measure on `U` giving
  `U ∩ K` volume one is `standardRadicalHaar E B`), both from Mathlib's
  `Measure.haarMeasure_unique` in the second-countable groups `K` and `U`.
- `normalizedParabolicConstantTerm_apply`: the value of the ordinary map is
  `δ m * ∫ u, ∫ k, φ ((k : G)⁻¹ * B.leviEmbedding E m * ((u : P) : G) * k)`.
- `normalizedTwistedParabolicConstantTerm_apply`: the value of the twisted map is
  `δ m * ∫ u, ∫ k, φ ((k : G)⁻¹ * B.leviEmbedding E m * ((u : P) : G) * entrywiseAut σ n k)`.
- `isLocallyConstant_normalizedAutParabolicConstantTerm` and
  `hasCompactSupport_normalizedAutParabolicConstantTerm`: the explicit function
  `m ↦ δ m * ∫ u, ∫ k, …` is locally constant and has compact support on `B.Levi E`.
  Neither is an input: the output of the map is an element of `SchwartzBruhat (B.Levi E)`,
  proved below.

Integrability on the actual fibres, for `parabolicConstantTermOfCompact` (so in
particular for the standard measures):

- `integrable_compactFibre`: for every `g ∈ G`, `k ↦ φ (k⁻¹ * g * θ k)` is integrable
  on `K`.
- `integrable_radicalFibre`: for every `m`, `u ↦ ∫ k, φ (k⁻¹ * m * u * θ k) dμK` is
  integrable on `U`.
- `integrable_productFibre`: for every `m`, `(u, k) ↦ φ (k⁻¹ * m * u * θ k)` is
  integrable on `U × K` for `μU.prod μK`.
- `parabolicConstantTermOfCompact_apply`, `_apply_swap` (for `SFinite μU`) and `_apply_prod`
  (for `SFinite μU`): the three evaluation formulas for arbitrary `K` and measures.

## Construction and proofs

The construction is a composite of three complex-linear maps, each landing in
Schwartz–Bruhat functions; the helper declarations are in the namespace
`Langlands.BaseChange.ParabolicConstantTerm`.

1. *Twisted compact average* (`twistedCompactAverage K θ hθ μK`, for a compact subgroup `K`
   of a Hausdorff topological group `G` and a continuous map `θ : G → G`):
   `g ↦ ∫ k, φ (k⁻¹ * g * θ k) dμK`. The kernel `(g, k) ↦ φ (k⁻¹ * g * θ k)` on `G × K`
   (`twistedConjugationKernel`) is `SchwartzBruhat.compLeftInverse` of the tensor
   `φ ⊗ 1_K` (`SchwartzBruhat.tensor`, with `constOne` the constant function one of the
   compact space `K`) along `(g, k) ↦ (k⁻¹ * g * θ k, k)`, which has the continuous left
   inverse `(g, k) ↦ (k * g * (θ k)⁻¹, k)`. The average is its
   `SchwartzBruhat.partialIntegral` over `K`; `integrable_twistedConjugation` is the
   integrability of the slices (`SchwartzBruhat.sliceSnd`, `SchwartzBruhat.integrable`).
2. *Radical integral* (`radicalIntegral B μU`, for any Hausdorff topological field `E`):
   `f ↦ (m ↦ ∫ u, f (m * u) dμU)`. The map `(m, u) ↦ m * u` is a homeomorphism
   `B.Levi E × U ≃ₜ P` (`leviRadicalHomeomorph`, with inverse `p ↦ (π p, (π p)⁻¹ * p)` for the
   Levi projection `π = B.leviProjection E`, built from `B.leviInParabolicContinuous E` and
   `B.leviProjectionContinuous E`); composed with the inclusion of the closed subgroup `P`
   (`B.isClosed_parabolic E`) it is a closed embedding `M × U → G`
   (`isClosedEmbedding_leviRadical`). Restriction of a Schwartz–Bruhat function along a
   closed embedding is Schwartz–Bruhat (`restrict`: local constancy by composition, compact
   support by `HasCompactSupport.comp_isClosedEmbedding`), and the radical integral is the
   partial integral over `U` of this restriction. This is where compact support of the output
   comes from: `P` is closed in `G`.
3. *Half modulus*: multiplication by the locally constant function
   `m ↦ δ_P(m)^{1/2}` (`mulLocallyConstant`). Local constancy
   (`isLocallyConstant_leviHalfModulus`) follows from `isLocallyConstant_of_isOpen_ker`
   (a homomorphism to `ℂˣ` with open kernel is constant on the open cosets of its kernel)
   and the Library's `LocalFieldData.isOpen_ker_leviHalfModulus`.

`parabolicConstantTermOfCompact` is the composite (3) ∘ (2) ∘ (1). Its evaluation theorem
unfolds the three values and reassociates `k⁻¹ * (m * u) * θ k`. For
`integrable_productFibre` the function on `U × K` is the restriction of the kernel of (1)
along the closed embedding `(u, k) ↦ (m * u, k)`, and is integrable for `μU.prod μK`, which
is finite on compact sets; the product σ-algebra contains the open sets because `K` is
second countable (`LocalFieldTopology.generalLinear_secondCountableTopology`). The other
order and the product form then follow from Mathlib's `integral_integral_swap` and
`integral_prod`.

## Scope

This module constructs the maps and proves their evaluation, integrability, local
constancy and compact support. It does not state or prove an orbital-integral descent
formula (Henniart–Lemaire II.4.5 (1), Laumon 4.4.9), a twisted character or van Dijk
formula (Henniart–Lemaire II.4.5 (2)), any compatibility with the Satake transform, or a
version with a central character.
