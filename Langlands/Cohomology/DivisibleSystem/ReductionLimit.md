# The inverse limit of the reductions L / ℓ ^ m L

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.IHomReduction` (`ihomReductionSystem`,
`ihomReductionTowerIso`, `reductionπ_ihomReductionIso_hom`),
`Langlands.Cohomology.DivisibleSystem.InverseLimit`
(`DivisibleSystem.inverseLimit`) and
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite.CompletenessProofs`
(`NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite`).
Through their imports it uses `powSMul_hom_apply`
(`Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`),
`reductionTower`, `reductionπ`, `reductionπIsCokernel`,
`powSMul_comp_reductionπ`, `reductionπ_map` and `reductionSystem`
(`Langlands.Cohomology.DivisibleSystem.Reduction`), and
`Induction.permutation`
(`Langlands.Representation.Induction.PermutationModule`). From Mathlib it uses
`IsAdicComplete` with `isAdicComplete_iff`, `IsHausdorff.haus`,
`IsPrecomplete.prec`, `SModEq.sub_mem`, `SModEq.zero`,
`Ideal.span_singleton_pow`, `Submodule.ideal_span_singleton_smul`,
`Submodule.mem_smul_pointwise_iff_exists`, the description of limits of types
`Types.isLimit_iff` and `Types.sectionOfCone`, `isLimitOfPreserves`,
`isLimitOfReflects`, `preservesSmallestLimits_of_preservesLimits`,
`reflectsSmallestLimits_of_reflectsLimits`,
`reflectsLimitsOfShape_of_reflectsIsomorphisms`,
`IsLimit.nonempty_isLimit_iff_isIso_lift`, `IsLimit.conePointUniqueUpToIso`,
`IsLimit.conePointUniqueUpToIso_hom_comp`, `IsLimit.postcomposeHomEquiv`,
`IsLimit.ofIsoLimit`, `Cone.ext`, the internal Hom of representations
`Rep.ihom` with `ihom.adjunction` and
`Adjunction.rightAdjoint_preservesLimits`, `Rep.epi_iff_surjective`,
`ShortComplex.exact_of_g_is_cokernel`,
`ShortComplex.exact_map_iff_of_faithful`, `ShortComplex.moduleCat_exact_iff`
and `Representation.trivial`.

## Conventions

`ℓ` and `m` are natural numbers and `R` is a commutative ring. `powSMul ℓ m X`
is the published endomorphism "multiplication by `ℓ ^ m`"; for a
representation its underlying map is `x ↦ ℓ ^ m • x` (`powSMul_hom_apply`).
The published `reductionTower ℓ L : ℕᵒᵖ ⥤ C` is the inverse system whose level
`m` is `cokernel (powSMul ℓ m L)`, written `L / ℓ ^ m L`, with transition maps
the projections `L / ℓ ^ m L ⟶ L / ℓ ^ n L` for `n ≤ m`, and
`reductionπ ℓ L m : L ⟶ L / ℓ ^ m L` is the projection; they commute with the
transition maps (`reductionπ_map`). When multiplication by `ℓ` is a
monomorphism on `L` (instance argument `[Mono (powSMul ℓ 1 L)]`), the
published `reductionSystem ℓ L` is the `ℓ`-divisible system with tower
`reductionTower ℓ L`, and the published `inverseLimit T` of an `ℓ`-divisible
system `T` is `limit T.tower`.

`IsAdicComplete (Ideal.span {(ℓ : R)}) N` is Mathlib's statement that the
`R`-module `N` is Hausdorff and complete for the `ℓ`-adic topology: elements
congruent to `0` modulo `(ℓ) ^ n • N` for every `n` are `0`, and every sequence
`f` with `f m ≡ f n` modulo `(ℓ) ^ m • N` for `m ≤ n` has a limit `x` with
`f n ≡ x` modulo `(ℓ) ^ n • N` for all `n`. For a representation `L` it is
stated for the underlying `R`-module, and "`L` is complete" below means this.
"`L` is finite over `R`" means `Module.Finite R L` and "`A` is projective over
`R`" means `Module.Projective R A`, for the underlying modules (instance
arguments). `Hom_R(A, L)` is Mathlib's `(Rep.ihom A).obj L`, the `R`-linear
maps `A → L` with `G` acting by conjugation; on morphisms `Rep.ihom A` is
composition.

## The cone of projections (namespace `Langlands.Cohomology.DivisibleSystem`)

`C` is an abelian category and `L` an object of `C`.

- `reductionCone ℓ L` is the cone over `reductionTower ℓ L` with vertex `L`
  and legs `reductionπ ℓ L m`; naturality is `reductionπ_map`.

## Limits of reductions of representations

`R : Type u`, `G : Type v` is a monoid and `L` is in `Rep.{w} R G`.

- `reductionπ_hom_apply_eq_zero_iff`: `reductionπ ℓ L m` sends `x` to `0`
  exactly when `x = ℓ ^ m • y` for some `y`. The sequence
  `L → L → L / ℓ ^ m L` (multiplication by `ℓ ^ m`, then `reductionπ`) is exact
  because `reductionπ` is a cokernel (`ShortComplex.exact_of_g_is_cokernel`),
  and it stays exact after the faithful forgetful functor to `ModuleCat R`
  (`ShortComplex.exact_map_iff_of_faithful`), where exactness is the stated
  property (`ShortComplex.moduleCat_exact_iff`); the converse is
  `powSMul_comp_reductionπ`.
- `reductionπ_hom_apply_eq_iff`: `x` and `y` have the same image in
  `L / ℓ ^ m L` exactly when `x ≡ y` modulo `(ℓ) ^ m • ⊤`, the submodule
  `Ideal.span {(ℓ : R)} ^ m • ⊤` of `L`. This submodule is the set of
  multiples `ℓ ^ m • y` (`Ideal.span_singleton_pow`,
  `Submodule.ideal_span_singleton_smul`,
  `Submodule.mem_smul_pointwise_iff_exists`), and the claim follows from the
  previous lemma applied to `x - y`.
- `nonempty_isLimit_reductionCone_iff ℓ L` (the main theorem): `reductionCone
  ℓ L` is a limit cone exactly when `L` is complete. The composite `F` of the
  forgetful functors `Rep R G ⥤ ModuleCat R ⥤ Type w` preserves and reflects
  limits indexed by `ℕᵒᵖ` (the forgetful functor of representations preserves
  and reflects limits, `preservesSmallestLimits_of_preservesLimits` and
  `reflectsSmallestLimits_of_reflectsLimits` for the index universe; the
  forgetful functor of modules reflects isomorphisms and preserves limits,
  hence reflects them, `reflectsLimitsOfShape_of_reflectsIsomorphisms`). So
  the cone is a limit exactly when its image under `F` is a limit of types,
  which by `Types.isLimit_iff` means: every compatible family `s` of elements
  `s m ∈ L / ℓ ^ m L` is the family of images of a unique `x ∈ L`. By
  `reductionπ_hom_apply_eq_iff` this unpacks as follows.
  If the cone is a limit, the uniqueness for the family of images of `0`
  gives the Hausdorff property, and a sequence `f` as in the definition of
  completeness gives the compatible family of images of `f m`, whose
  preimage `x` is the required limit. Conversely, if `L` is complete, choose
  preimages `g m` of `s m` (`reductionπ` is an epimorphism, hence surjective by
  `Rep.epi_iff_surjective`); compatibility of `s` gives `g m ≡ g n` modulo
  `(ℓ) ^ m • ⊤` for `m ≤ n`, completeness (`IsPrecomplete.prec`) gives `x`
  with image `s m` for every `m`, and if `y` has the same images then `y - x`
  lies in every `(ℓ) ^ m • ⊤`, so `y = x` (`IsHausdorff.haus`).
- `isIso_limit_lift_reductionCone_iff`: equivalently, the canonical map
  `limit.lift (reductionTower ℓ L) (reductionCone ℓ L)` from `L` to the limit
  is an isomorphism exactly when `L` is complete
  (`IsLimit.nonempty_isLimit_iff_isIso_lift`).

Below `L` is complete (hypothesis `hL`).

- `isLimitReductionCone ℓ hL`: the limit cone structure on `reductionCone ℓ L`
  given by the main theorem (chosen with `Nonempty.some`).
- `reductionLimitIso ℓ hL : limit (reductionTower ℓ L) ≅ L` is the comparison
  of the chosen limit with `isLimitReductionCone`
  (`IsLimit.conePointUniqueUpToIso`); `reductionLimitIso_hom_reductionπ`: its
  composite with `reductionπ ℓ L m` is the limit projection at `m`.
- `reductionSystemLimitIso ℓ hL : inverseLimit (reductionSystem ℓ L) ≅ L`
  is `reductionLimitIso` for the published reduction system, when
  multiplication by `ℓ` is a monomorphism on `L`.

## Finite representations

- `isAdicComplete_of_finite ℓ L`: if `R` is Noetherian and itself
  `ℓ`-adically complete (instance argument
  `[IsAdicComplete (Ideal.span {(ℓ : R)}) R]`), every `L` in `Rep.{w} R G`
  that is finite over `R` is complete. This is the published NYLL theorem
  `isAdicComplete_of_moduleFinite` (a finite module over a Noetherian ring
  complete for an ideal `I` is `I`-adically complete) applied to the
  underlying module and `I = (ℓ)`; it is not reproved here.

## Hom into a complete representation

`R : Type u`, `G : Type v` is a group and `A`, `L` are in `Rep.{u} R G`:
Mathlib's adjunction `A ⊗ - ⊣ Rep.ihom A` (`ihom.adjunction`) requires the
carriers to be in the universe of `R`.

- `ihom_preservesLimitsOfShape_nat`: `Rep.ihom A` preserves limits indexed by
  `ℕᵒᵖ`, being a right adjoint (`Adjunction.rightAdjoint_preservesLimits`).

Below `L` is complete (hypothesis `hL`).

- `isLimitIhomReductionCone ℓ A hL`: the image of `reductionCone ℓ L` under
  `Rep.ihom A`, with vertex `Hom_R(A, L)` and legs composition with
  `reductionπ ℓ L m`, is a limit cone (`isLimitOfPreserves`).
- `ihomReductionLimitIso ℓ A hL : limit (reductionTower ℓ L ⋙ Rep.ihom A) ≅ Hom_R(A, L)`,
  that is `lim_m Hom_R(A, L / ℓ ^ m L) ≅ Hom_R(A, L)`, is the comparison with
  this limit cone; `ihomReductionLimitIso_hom_map_reductionπ`: its composite
  with composition by `reductionπ ℓ L m` is the limit projection at `m`.
- `ihomReductionSystemLimitIso ℓ A hL : inverseLimit (ihomReductionSystem ℓ A L) ≅ Hom_R(A, L)`:
  the same for the published system `ihomReductionSystem ℓ A L` (levels
  `Hom_R(A, L / ℓ ^ m L)`), when `A` is projective over `R` and
  multiplication by `ℓ` is a monomorphism on `L`; its tower is
  `reductionTower ℓ L ⋙ Rep.ihom A` by definition.
- `isAdicComplete_ihom ℓ A hL`: if `A` is projective over `R`, `Hom_R(A, L)`
  is complete. By the main theorem it suffices that `reductionCone ℓ
  Hom_R(A, L)` is a limit. Its image under the isomorphism of towers
  `ihomReductionTowerIso ℓ A L` (published:
  `Hom_R(A, L) / ℓ ^ m ≅ Hom_R(A, L / ℓ ^ m L)`, compatible with the
  projections by `reductionπ_ihomReductionIso_hom`) is the limit cone
  `isLimitIhomReductionCone`, and limit cones transfer along isomorphisms of
  diagrams (`IsLimit.postcomposeHomEquiv`, `IsLimit.ofIsoLimit`, `Cone.ext`).

## Harris's permutation modules

`R : Type u` is Noetherian and `ℓ`-adically complete, `G : Type v` is a group
acting on `X : Type u`, `M` is a free and `L` a finite `R`-module, both in
`Type u`. `Induction.permutation R G X M` is the published permutation
representation on `M[X] = X →₀ M`, and `Representation.trivial R G L` is `L`
with the trivial action.

- `permutationIhomReductionLimitIso ℓ`: the inverse limit over `m` of
  `Hom_R(M[X], L / ℓ ^ m L)` is isomorphic to `Hom_R(M[X], L)`. This is
  `ihomReductionLimitIso` with `L` complete by `isAdicComplete_of_finite`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999) (Worker 61 read the rendered scanned pages):

- §4, printed p.311 (one-based PDF page 13): "Now we want to let `m` vary.
  Let the `K_ℓ`-modules `(ρ, W)` and `𝓛 = 𝓛_W` be as in §3; let
  `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. Then `𝓛_m` forms an inverse system of
  `𝒪`-modules, and the inverse system `{𝓛̃_m}` defines a lisse `ℓ`-adic sheaf
  `W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ` on `S̄_K(N)`." On the same page (4.8)
  identifies a module of automorphic forms with coefficients `𝓛_m` with
  `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`.
- proof of Proposition 4.10, printed p.312 (one-based PDF page 14): "In fact,
  we have proved the stronger (integral) statement (4.10.4)
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪(n − 1)), 𝒜_ℓ(GJ, 𝓛, H)) ⇒ H^{i+j}(S̄_K(N), 𝓛̃)`."

Harris passes from the spectral sequences (4.9), with coefficients
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`, to statements with coefficients `𝓛` by taking
limits over `m`. He does not state that `𝓛` is the inverse limit of the
`𝓛_m`, nor that the inverse limit of the `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` is
`Hom(𝒪[C_p/H_p]^M, 𝓛)`; this module proves both, for the Lean models, as our
reading of that passage to the limit. In Harris's setting, §3 (printed
p.306, one-based PDF page 8) fixes the convention "`L_v = L ⊗_ℚ ℚ_v`" for a
place `v` of `ℚ`, so `L_ℓ = L ⊗_ℚ ℚ_ℓ` is in general a finite product of
finite extensions of `ℚ_ℓ`, one for each place of `L` above `ℓ`, not a single
field. On printed p.307 (one-based PDF page 9) "`𝒪` denote[s] the ring of
integers of `L_ℓ`" and `𝓛_W` is "a `K_ℓ`-stable `𝒪`-lattice in `W(L)`". We
read `𝒪` as the integral closure of `ℤ_ℓ` in `L_ℓ`, which is the finite
product of the rings of integers of these factors. Each factor is a complete
discrete valuation ring in which `ℓ` generates a power of the maximal ideal,
so `𝒪` is Noetherian and `ℓ`-adically complete, and the lattice `𝓛` is a
finitely generated `𝒪`-module. These facts about `𝒪` are not formalized and
enter `permutationIhomReductionLimitIso` as hypotheses on `R`: a commutative
Noetherian ring that is complete for the ideal generated by `ℓ`, which
includes this finite product of rings. As in the
published IHomReduction module, `R` plays the role of `𝒪`, `L` of `𝓛`,
`L / ℓ ^ m L` of `𝓛_m` (the identification `𝓛 ⊗_𝒪 𝒪/ℓ^m𝒪 ≅ 𝓛/ℓ^m𝓛` is not
formalized), and `M[X]` of `𝒪[C_p/H_p]^M` with `X = C_p/H_p`. The
statements, the formulation through `IsAdicComplete` and all proofs are ours;
the completeness of finite modules is the published NYLL theorem. The module
is derived.

## Scope

The Lean modules are `Hom_R(M[X], L / ℓ ^ m L)` and `Hom_R(M[X], L)`, the
`R`-linear maps; their identification with Harris's
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` (maps of `𝒪_m`-modules) is not formalized. The
module does not construct Harris's `ℓ`-adic sheaves `W̃` or `𝓛̃`, the
spectral sequences (4.9), (4.10.1), (4.10.4), or the identifications (4.7),
(4.8); it does not prove that the limit over `m` commutes with cohomology. The
results about `Hom_R(A, -)` require `G` a group and the carriers in the
universe of `R`. Everything concerns the categories `Rep` of representations
of abstract monoids or groups, not categories of smooth representations.

Worker 13's published `Langlands.Coefficients.AdicSystem` builds, for an
`R`-module `M` and an ideal `I`, the inverse system `M / I ^ n M` in
`ModuleCat R` (`AdicSystem.system`) and proves that Mathlib's
`AdicCompletion I M` is its limit (`AdicSystem.completionConeIsLimit`); its
Markdown leaves open whether `M` itself is that limit. This module works
instead with the published `reductionTower ℓ L` of the `ℓ`-divisible-system
framework, in `Rep R G` (cokernels of multiplication by `ℓ ^ m`), and proves
that `L` is its limit exactly when `L` is `ℓ`-adically complete. It does not
import `AdicSystem`, and no comparison between the two towers is formalized.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
