# Passage of the cuspidal tests of Eisenstein series to a standard parabolic: proof

Module `Langlands.Global.AdelicEisensteinCuspidalTestStandardizationProof` proves
`Langlands.Global.EisensteinCuspidalTestStandardizationStatement` (module
`Langlands.Global.AdelicEisensteinCuspidalTestStandardizationReduction`, whose Markdown explains
the statement) as `Langlands.Global.eisensteinCuspidalTestStandardization`, in universe `u`.
The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The witnesses are `m = 1`, a standard index `I` with a rational point `s` conjugating `P` onto
`P_I`, `iota` the restriction of characters along the induced identification `P_I ≅ P`,
`φ' 0 = φ(s⁻¹ ·)` and `E 0 (λ) = exp(-⟨λ, H'(s)⟩)`, where `H'` is the height of the conjugated
parabolic `s P s⁻¹` for the compact `K`. The tested identity then holds for every `λ` (the bound
`R = 0` is not used), and no integrability is needed.

## Helper results

### Root forms (sections `RootForms`, `TorusForms`, `TorusComparison`)

- `ParabolicRootPresentation.realRootFunctional_comp_eq`: for a Levi lift `t` of the
  presentation torus (`t ≫ l ≫ p = r.data.i`) and a character `β` of the torus, the real root
  form of `f ≫ β` at `x` is the Weyl-invariant form `B_T(x|_T, β)` of the torus, where `x|_T` is
  the restriction through `t ≫ l`. It combines `eisensteinAmbientParameterLift` with the
  compatibility `weylInducedCharacterForm_compatible` of the induced form on the split component.
- `ParabolicRootPresentation.realRootFunctional_compAmbientIso`,
  `ParabolicRootPresentation.rootFunctional_compAmbientIso`,
  `ParabolicRootPresentation.unipotentRoots_compAmbientIso`: transport of a presentation through
  an ambient isomorphism (`ParabolicRootPresentation.compAmbientIso`) changes neither the root
  forms nor the roots in the unipotent radical
  (`weylInducedCharacterForm_comp_ambientIso`, `positiveRelativeRoots_comp_iso`).
- `characterRealCongr_relativeWeylRealCharacterAction`: an isomorphism of tori over the ambient
  group intertwines the two real relative Weyl actions (`relativeWeylCharacterAction_transport`).
- `weylInvariantForms_root_proportional`: two Weyl-invariant inner products `B`, `C` on
  `X^*(T) ⊗ ℝ` satisfy `C(x, β) = c_β B(x, β)` with `c_β = C(β, β) / B(β, β) > 0` for every
  relative root `β`. Both sides follow from the coroot formula
  `⟨x, β^∨⟩ B(β, β) = 2 B(x, β)` (`RelativeRootReflectionData.coroot_mul_form`) for a root
  reflection datum (`relativeRootReflectionExistence`).
- `ParabolicRootPresentation.rootFunctional_torusComparison`: let `r`, `s` be two presentations of
  one parabolic, Levi and split component, with a torus isomorphism `e` such that
  `r.data.i = e ≫ s.data.i` and `s.data.f = r.data.f ≫ e`. Then every root `α` of `r` in the
  unipotent radical is one of `s`, and `s.rootFunctional α = c · r.rootFunctional α` for some
  `c > 0`. The roots agree by `unipotentRoots_eq_intrinsicPositiveRoots` and
  `intrinsicPositiveRoots_eq`. For `α = r.data.f ≫ β` with `β` a positive root, the root form of
  `s` at `α = s.data.f ≫ (e⁻¹ ≫ β)` is the form of `s.data.T` at the restriction through the lift
  `e⁻¹ ≫ t`, that is, the pull-back `C` of that form along `e` at the restriction through `t`. `C`
  is again Weyl invariant for `r.data.i`, so `weylInvariantForms_root_proportional` gives the
  factor `c_β`. The complex forms are compared on pure tensors.

### `rootPresentationRootFunctionalComparison`

Let `r₁`, `r₂` be presentations of parabolics `p₁ : P₁ → G`, `p₂ : P₂ → G` with
`e : P₂ → P₁`, `e ≫ p₁ = p₂`, equal images and Levis of equal image. For every root `β₁` of
`r₁` in the unipotent radical there are a root `β₂` of `r₂` in the unipotent radical and
`c > 0` with `r₁.rootFunctional β₁ λ = c · r₂.rootFunctional β₂ (λ|_{P₂})` for every `λ`.

The first four steps repeat those of `rootPresentationRegularityComparison` (module
`Langlands.Global.AdelicEisensteinRegularityPresentationComparison`):

1. the Levis are identified by `IsClosedSubgroup.sourceIsoOfRangeEq`, and both presentation tori
   lift to the Levis (`ParabolicRootPresentation.exists_leviTorusLift`);
2. `smoothMaximalSplitTorusConjugacy` in the Levi `M₁` gives a rational point `z` of `M₁` and an
   isomorphism `φ : T₂ ≅ T₁` with `r₂.data.i ≫ inner(g) = φ ≫ r₁.data.i` in `G`, where `g` is the
   image of `z`;
3. `r₂' = r₂.compAmbientIso (inner g)` is a presentation of `p₂ ≫ inner(g)`, whose image and Levi
   image are those of `p₁` and `l₁ ≫ p₁`, because `g` lies in the Levi;
4. the data `⟨T₂, r₂.data.i ≫ inner(g), ν₂, J₂, r₁.data.f ≫ φ⁻¹⟩` form a presentation `s` of
   `(p₁, l₁, a₁)`.

Then `rootFunctional_torusComparison` for `r₁` and `s` gives `β₁ = (r₁.data.f ≫ φ⁻¹) ≫ χ` for a
positive root `χ` of `r₂.data.i ≫ inner(g)`, with `s.rootFunctional β₁ = κ · r₁.rootFunctional β₁`
and `κ > 0`. Take `β₂ = r₂.data.f ≫ χ` and `c = κ⁻¹`. It is nonzero, because `restrict_positiveRoot_eq_zero_iff`
characterizes the vanishing of both restrictions by the same simple roots `J₂`, and `χ` is a
positive root of `r₂.data.i` (`positiveRelativeRoots_comp_iso`). The presentations `s` (of `p₁`)
and `r₂'` (of `p₂ ≫ inner(g)`) share the torus, the inclusion, the cocharacter and the simple
roots. With `j = e ≫ inner_{P₁}(z)`, `j ≫ p₁ = p₂ ≫ inner(g)`, the root-form transport
`rootFunctional_parameterRestrict_eq_of_comp_eq` (module
`Langlands.Global.AdelicIntertwiningStandardizationProof`) gives
`r₂'.rootFunctional β₂ (λ|_j) = s.rootFunctional β₁ λ`. Finally, `λ|_j = λ|_e` by
`parameterRestrict_comp_innerIso_hom`, and `r₂'.rootFunctional β₂ = r₂.rootFunctional β₂` by
`rootFunctional_compAmbientIso`.

### Scalar factors in the tests

`StandardParabolicFamily.constantTerm_const_mul` and `StandardParabolicFamily.leviPairing_const_mul`:
the constant term `C_J` and the pairing `(·(· g), ψ)` over `M_J(F) \ M_J(𝔸)^1` commute with
multiplication by a scalar `c`. Both are integrals, and `MeasureTheory.integral_const_mul` holds
without any integrability hypothesis.

## Proof of `eisensteinCuspidalTestStandardization`

1. **Standard conjugate.** `StandardParabolicFamily.exists_standardConjugate` (module
   `Langlands.Global.AdelicIntertwiningStandardizationProof`), applied to `p`, `iU`, `l`, gives a
   standard index `I`, a rational point `s`, isomorphisms `eP : P_I ≅ P` with
   `eP ≫ p ≫ inner(s) = p_I` and `κ : M_I ≅ M` with `κ ≫ l = l_I ≫ eP`, and the equality of the
   images of the unipotent radicals `iU ≫ p ≫ inner(s)` and `iU_I ≫ p_I`. Hence `p_I` and
   `p' = p ≫ inner(s)` have the same image, and so do `l_I ≫ p_I` and `l ≫ p'`. `K` is Iwasawa for
   `p_I` (`StandardParabolicFamily.isIwasawaCompact_of_minimal` with `h₀`), hence for `p'`
   (`IsIwasawaCompact.of_range_eq`).
2. **Parameters.** `iota = parameterRestrictIsoEquiv eP`, restriction of characters along `eP`;
   its inverse is restriction along `eP⁻¹`.
3. **Inducing function.** `φ' = φ(s⁻¹ ·)` is automorphic on `U_I(𝔸) M_I(F) \ G(𝔸)`:
   `IsAutomorphicFunctionOn.leftTranslate` (module
   `Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation`) gives automorphy for the
   conjugate of the left invariance subgroup by `s`. That conjugate is the subgroup of `p'`
   (`parabolicQuotientSubgroup_conjugate`), which is the subgroup of `p_I` by the equal images
   (`parabolicQuotientSubgroup_eq_of_range_eq`). The automorphy predicate takes its differential
   hypothesis as a proposition, so the one of `𝓕.IsAutomorphicOn` can replace `hcalc`.
4. **Series.** `IsIwasawaCompact.eisensteinSeries_conjugate_parabolic` (module
   `Langlands.Global.AdelicEisensteinConjugateParabolicSeries`) gives
   `E_{p'}(φ', λ) = e^{⟨λ, H'(s)⟩} E_P(φ, λ)`. `IsIwasawaCompact.eisensteinSeries_eq_of_range_eq`
   (module `Langlands.Global.AdelicEisensteinParabolicRangeTransport`) along `eP` gives
   `E_{p'}(φ', λ) = E_{P_I}(φ', iota λ)`. With `IsIwasawaCompact.heightPower_neg_mul`,
   `E_P(φ, λ) = e^{-⟨λ, H'(s)⟩} E_{P_I}(φ', iota λ)` as functions on `G(𝔸)`, for every `λ`.
5. **Coefficient.** `E 0 ∘ e` is the exponential of the linear form
   `v ↦ ⟨-(e v), H'(s)⟩`, hence differentiable.
6. **Instances.** `Fintype (relativeWeylGroup 𝓕.i)` is `Fintype.ofFinite` of
   `IsConnectedReductive.finite_relativeWeylGroup`. The monomorphism property of `𝓕.f J` follows
   from the factorization `factor_comp` of `𝓕.isCompatible J` through the monomorphism
   `a_J ≫ l_J ≫ p_J` (`mono_of_mono_fac`).
7. **Regularity.** Let `r' = r.compAmbientIso (inner s)`, a presentation of `p'`.
   `rootPresentationRegularityComparison`, for `𝓕.rootPresentation I` and `r'` with
   `eP⁻¹ : P → P_I`, `eP⁻¹ ≫ p_I = p'`, gives for each `R` a bound `R'` such that `iota λ` is
   `R`-regular whenever `(iota λ)|_{eP⁻¹} = λ` is `R'`-regular for `r'`.
   `eisensteinRegularityAmbientTransport` identifies regularity for `r'` with regularity for `r`.
8. **Root forms.** `rootPresentationRootFunctionalComparison` for the same data gives, for a root
   `β'` of `A_I` in `U_I`, a root `β` of `r'` (a root of `r` by `unipotentRoots_compAmbientIso`) and
   `c > 0` with `B_I(iota λ, β') = c · B_{r'}(λ, β) = c · B_r(λ, β)`
   (`rootFunctional_compAmbientIso`); `s = c` is nonzero.
9. **Tests.** By step 4 and the scalar lemmas,
   `(C_J E_P(φ, λ)(· g), ψ) = E 0 (λ) · (C_J E_{P_I}(φ', iota λ)(· g), ψ)`, which is the sum over
   `Fin 1` (`Fin.sum_univ_one`).

## Relation to the literature

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024) (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), §2.1–§2.2, and
Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995)
(`moeglin-waldspurger-1995-spectral-decomposition`), I.1.4 and II.1.5, work only with standard
parabolics and a compact in good position. The proof follows the rational-conjugation argument
of the statement's Markdown, with three differences in the implementation. The height scalar is
taken at `s` for the conjugated parabolic `s P s⁻¹`, through the published conjugation
identity, rather than as `H_P(γ⁻¹)`. The parameter map is restriction of characters along the
identification of `P_I` with `P` over the conjugated embedding. The maximal split tori are
compared inside the common Levi of `P_I` and the conjugated `P`, by the conjugacy of maximal
split tori there, rather than by a further element of `M_I(F)` in `G`. The positive factors
between root forms are the per-root ratios `C(β, β) / B(β, β)` of the two Weyl-invariant forms,
from the coroot formula.
