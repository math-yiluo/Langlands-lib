# Reduction of rational natural induction duality to a uniform integral duality

Module `Langlands.Representation.Aubert.General.RationalInductionDualityReduction`,
namespace `Langlands.Aubert.General`.

## Purpose and scope

This module is partial progress towards the proof target
`Langlands.Aubert.General.RationalPointFamily.RationalNaturalInductionDualityStatement`
of task `2137e0ce-8d32-43f5-b4ed-79824b68585f`. That statement asks, for the
actual standard parabolic `P = M ⋉ U` of the rational-point group `G(k)` of a
connected reductive group over a nonarchimedean local field, for a natural family
of isomorphisms `i(A)∨ ≅ i(A∨)` on admissible smooth `M`-representations `A`, where
`i` is `normalizedInductionFunctor` and `∨` is the smooth contragredient.

The module does not prove the target. It proves the parts of the argument that need
no compact-picture integral, and it identifies the actual standard parabolic with a
dynamic parabolic. The remaining analytic input is an integral-characterized
duality equivalence for each admissible `A` with one measure for all `A`. That
input is the hypothesis `IsUniformIntegralDuality` below. The module assumes no
compactness, unimodularity or Iwasawa decomposition as a global hypothesis: each
theorem states the hypotheses it uses.

## Provenance

All declarations are internal proof devices made for this task (provenance
`internal`). The mathematics is the standard argument for
same-parabolic duality `i(σ)∨ ≅ i(σ∨)` through the pairing
`⟨ℓ, f⟩ = ∫_K ⟨ℓ(k), f(k)⟩ dk` (Casselman, lecture notes *Introduction to
representations of p-adic groups*, Chapter III "Induced representations and the
Jacquet module", 2019 revision, section 1, Proposition III.1.1). This is context
only: no declaration transcribes a definition from that source.

`smoothContragredientEquiv` reuses the common construction in
`Smooth.Contragredient.Equivalence`, extracted unchanged from the published
`Langlands.Classification.HighestDerivativeSupportShiftProof.smoothContragredientEquiv`.
Both namespaces retain abbreviations for that definition. Credit for the
construction belongs to the authors of the original module.

## Section `Contragredient`

`smoothContragredientEquiv e` sends an equivalence of representations
`e : ρ ≃ σ` to the equivalence `σ∨ ≃ ρ∨` of smooth contragredients. The forward map
is `contragredientMap e` (precomposition `ℓ ↦ ℓ ∘ e`). It is injective because `e`
is surjective, and surjective because `ℓ = (ℓ ∘ e⁻¹) ∘ e`.

## Section `Generic`

Here `G` is a locally compact nonarchimedean topological group and
`h : IsSemidirectDecomposition P M U` is an actual semidirect decomposition of a
subgroup `P` with Levi `M`, unipotent radical `U` and projection
`h.projection : P →* M`.

- `compactOpenCofinal_of_isClosed`: a closed subgroup `M` has compact open
  subgroups inside every open subgroup. Proof: `M` is locally compact and
  nonarchimedean, so the published `compactOpenSubgroupBasis` applies. The
  closedness of the Levi subgroup is not proved here. When `G` is Hausdorff, `P` is
  closed and the projection is continuous, it is the published
  `IsSemidirectDecomposition.isClosed_levi` of
  `Langlands.Representation.Aubert.General.RationalInvolutivityReduction`.
- `closedHalfCharacter_mul_self`: for `q ∈ P`, the square of the induction
  character `δ^{1/2}(q) = closedHalfCharacter U hU P q` is the restricted Haar
  modulus `closedRestrictCharacter U hU P q`, as complex numbers. Proof: the
  published identity `HaarModulus.halfCharacter_sq`, read in `ℂ`.
- `inducingRepresentation_isAdmissible`: if `A` is admissible and the projection
  is continuous, then the inducing representation
  `p ↦ δ^{1/2}(p) A(projection p)` of `P` is admissible. Smoothness comes from the
  published `Induction.exists_twist_comp_fixed`. For finiteness, let `H` be an
  open subgroup of `P`. Take the open subgroup `N` of `M` that is the preimage of
  `H ∩ ker δ^{1/2}` under the inclusion `M ≤ P`. Every `H`-fixed vector is
  `N`-fixed, because on `N` the character is trivial and the projection is the
  identity. So the `H`-fixed vectors form a submodule of the finite-dimensional
  `N`-fixed vectors of `A`.
- `smoothInduced_inducingRepresentation_isAdmissible` and
  `normalizedInductionFunctor_obj_isAdmissible`: if `P \ G`
  (`Induction.LeftQuotient P`) is compact, then smooth induction of the inducing
  representation of an admissible `A` is admissible. Proof: the published
  `Induction.smoothInduced_isAdmissible_of_compactSpace`. The first form is stated
  on the representation `Induction.smoothInduced P (inducingRepresentation h hU A)`.
  The second form is stated on the bundled object `i(A)`. The two are
  definitionally equal, but the first form avoids an expensive unfolding when it
  is passed to theorems stated on representations.
- `IsUniformIntegralDuality h hU K μ` (definition, a `Prop`): for a subgroup `K`
  of `G` with a measure `μ`, every admissible `A` has an equivalence of
  representations `E : i(A)∨ ≃ i(A∨)` such that for all `ℓ ∈ i(A)∨` and
  `f ∈ i(A)`,
  `⟨ℓ, f⟩ = ∫_K ⟨E(ℓ)(k), f(k)⟩_A dμ(k)`.
  Here `⟨·,·⟩_A` is the pairing of `A∨` with `A` and `E(ℓ)(k)`, `f(k)` are the
  values of the induced functions at `k` (`Induction.eval`). The measure `μ` and
  the subgroup `K` are the same for every `A`. This is the form in which the
  compact-picture duality is used, with `K = ⊤` and a Bruhat-function measure.
- `exists_natural_of_isUniformIntegralDuality`: a uniform integral duality gives a
  family of isomorphisms `E A hA : i(A)∨ ≅ i(A∨)` of bundled smooth representations,
  natural on admissible objects:
  `contragredientHom (i f) ≫ (E A hA).hom = (E B hB).hom ≫ i (contragredientHom f)`
  for every `f : A ⟶ B`. This conclusion has the exact shape of the target's
  conclusion. The isomorphisms are `SmoothRep.mkIso` of the chosen equivalences.
  Naturality: for `ℓ ∈ i(B)∨` it must be shown that
  `E_A(ℓ ∘ i(f)) = i(f∨)(E_B ℓ)`. Write the right side as `E_A(E_A⁻¹(…))`; it
  then suffices that the functionals `ℓ ∘ i(f)` and `E_A⁻¹(i(f∨)(E_B ℓ))` on `i(A)`
  agree at every `x ∈ i(A)` (Subtype and linear-map extensionality). By the
  integral formula for `B`, the first value is
  `∫_K ⟨E_B(ℓ)(k), f(x(k))⟩_B dμ(k)`. By the integral formula for `A`, the second
  value is `∫_K ⟨f∨(E_B(ℓ)(k)), x(k)⟩_A dμ(k)`. The integrands agree by the
  definition of the contragredient map, so the last step is `rfl`.
- `exists_functorEquiv_of_twistEquiv`: an integral-characterized equivalence in the
  form returned by `Induction.exists_integralDualEquiv` (source
  `(smoothInduced P (inducingRepresentation A))∨`, target
  `smoothInduced P (twist δ^{1/2} (A∨ ∘ projection))`) gives one in the form used by
  `IsUniformIntegralDuality`, with the same integral formula. The two forms are
  definitionally equal. The proof composes with identity equivalences `e0` and
  `e2` between the two spellings of `i(A)` and `i(A∨)` and with
  `smoothContragredientEquiv e0.symm`. This avoids asking Lean to unify the two
  smooth-dual carrier types, which is very slow.

## Section `Rational`

Here `k` is a field, `G` an affine group scheme over `Spec k`, `i : T → G` a torus
and `ν` a cocharacter of `T`. `parabolic i ν I` is the rational-point standard
parabolic of `Langlands.Aubert.General.RationalPointFamily`.

- `exists_parabolic_eq_dynamic`: assume `StandardCocharacterStatement`, `G`
  connected reductive, `i` a maximal split torus and `ν` generic. Then for each
  finite set `I` of simple roots, `parabolic i ν I` is the set of `k`-points of the
  dynamic parabolic `Dynamic.parabolic χ` of some cocharacter
  `χ : 𝔾ₘ → G`. Proof: `parabolic i ν I` is by definition the `k`-points of
  `standardParabolic i ν (rootSet i ν I)`. The standard-cocharacter statement gives
  a cocharacter `ζ` of `T` with the equality of subgroup schemes
  `standardParabolic i ν (rootSet i ν I) = Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)`
  (applied with `J = rootSet i ν I ⊆ simpleRelativeRoots i ν`). Take
  `χ = CommGroupScheme.groupHom ζ ≫ i`.
- `compactSpace_leftQuotient_parabolic`: assume in addition that `k` is a
  nonarchimedean local field, and assume
  `BruhatTits.DynamicParabolicQuotientCompactStatement`. Then the right-coset space
  `P \ G(k)` of `P = parabolic i ν I`, with the point topology on `G(k)`, is
  compact. Proof: rewrite `P` as a dynamic parabolic with
  `exists_parabolic_eq_dynamic` and apply the compactness statement.

## Use

The module `Langlands.Representation.Aubert.General.RationalInductionDualityAssembly`
combines these results with the Bruhat-function measure of
`Langlands.Representation.Induction.CompactQuotientDuality`, with the closed-Levi
lemma of `RationalInvolutivityReduction` and with
`RationalParabolicModulusStatement`. It is a separate module so that this one
does not import those modules.
