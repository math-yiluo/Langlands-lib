# Root forms of the standard parabolics of a family

Module `Langlands.Global.AdelicStandardRootFunctional`, namespace
`Langlands.Global.StandardParabolicFamily`. It is a helper module for the proof
`Langlands.Global.intertwiningElementaryChain` and has no statement of its own.

## Setting and notation

`fam : StandardParabolicFamily F G` over a number field `F` (module
`Langlands.Global.AdelicLeadingCuspidalComponents`) with maximal split torus `T` (`fam.i`),
generic cocharacter `fam.ν`, standard parabolics `P_J = M_J U_J`, split components `A_J`
and maps `f_J : A_J → T`. The root forms are those of the presentations
`fam.rootPresentation J` (module `Langlands.Global.AdelicIntertwiningElementaryChainStatement`):
for a character `α` of `A_J`, `realRootFunctional α x = B_{A_J}(x|_{A_J}, α)` on
`X^*(P_J) ⊗ ℝ`, and `rootFunctional` is its complexification. `B_T = torusForm` is the
Library's Weyl-invariant positive form `relativeWeylInvariantForm` on `X^*(T) ⊗ ℝ`.

Assumptions. `torusForm` and the declarations that use it assume
`[Fintype (relativeWeylGroup fam.i)]`. The root-form identities, starting with
`realRootFunctional_eq`, also assume the monomorphism instances
`[∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left]` of the split-component maps.
Both are hypotheses of the target statement. Declarations that do not use them
(`ker_restrictReal_splitComponent`, `torus_comp_weylConjugation`,
`linearIndependent_simpleRoots_real`, `one_tmul_notMem_span`, `restrict_simple_ne_zero`,
`restrict_simple_mem_unipotentRoots`) omit them.

## Restriction to the maximal split torus

* `torusRestrictReal J`: restriction `X^*(P_J) ⊗ ℝ → X^*(T) ⊗ ℝ` along `fam.torus J ≫ fam.l J`.
* `splitComponent_comp_levi` and `realParameterRestriction_eq`: `a_J ≫ l_J` factors as
  `f_J ≫ torus_J ≫ l_J`, so restriction to `A_J` is restriction to `T` followed by restriction
  along `f_J`.
* `torusRestrictReal_injective`: from the Library's
  `realParameterRestriction_splitComponent_injective`.
* `torusRestrictReal_mem_corootAnnihilator` and `range_restrictReal_torus`: the image of
  `X^*(M_J) ⊗ ℝ` in `X^*(T) ⊗ ℝ` is the coroot annihilator of `J`
  (`standardLeviCharacterAnnihilator`).
* `torus_comp_factor`: compatibility of the torus maps with an inclusion `P_J → P_L`.
* `ker_restrictReal_splitComponent`: the kernel of restriction along `f_J` is the real span of
  `J` (`standardLeviCentralDirections`, `ker_restrictReal_eq_rootSpan_of_range`).
* `torusRestrictReal_mem_orthogonal`: `x|_T` is `B_T`-orthogonal to that kernel
  (`corootAnnihilator_eq_orthogonal`).

## Root forms through the torus

* `realRootFunctional_eq`: for `β ∈ X^*(T)`, the root form of `β ∘ f_J` is
  `x ↦ B_T(x|_T, β)`. The Library's `weylInducedCharacterForm_compatible` gives
  `B_{A_J}(u|_{A_J}, v|_{A_J}) = B_T(L(u|_{A_J}), v)` for the orthogonal lift `L`; since
  `β − L(β|_{A_J})` lies in the kernel of restriction and `x|_T` is orthogonal to it, the two
  values agree.
* `exists_restrictReal_of_realRootFunctional_eq_zero`: let `α` be a simple root, `L` the index
  with `L = J ∪ {α}` and `e : P_J → P_L` the inclusion. If the root form of `α ∘ f_J` vanishes at
  a real `x`, then `x = y|_{P_J}` for some `y ∈ X^*(P_L) ⊗ ℝ`. Indeed `B_T(x|_T, α) = 0` makes
  `x|_T` vanish on the coroot of `α` (`RelativeRootReflectionData.coroot_eq_zero_iff`), so
  `x|_T` lies in the coroot annihilator of `L`, the image of `X^*(M_L) ⊗ ℝ`; precomposing with
  a retraction `P_L → M_L` gives `y`, and injectivity of `torusRestrictReal J` gives
  `y|_{P_J} = x`.
* `exists_parameterRestrict_of_rootFunctional_eq_zero`: the same for complex parameters, by
  splitting `ν` into real and imaginary parts (`ImaginaryAxis.complexify`,
  `ImaginaryAxis.rootFunctional_complexify`).

## Transport by Weyl parameters

* `torus_comp_weylConjugation`: for a normalizer point `W` and a Weyl conjugation `(W, C)` from
  `P_I` to `P_K`, `torus_K ≫ C ≫ l_I = σ⁻¹ ≫ torus_I ≫ l_I`, where `W` normalizes `T` through
  `σ = normalizingAut`.
* `rootFunctional_weylParameter`: the root form of `γ ∘ f_K` at `weylParameter l_I C π ν` is
  the root form of `(W⁻¹ γ) ∘ f_I` at `ν`, for every retraction `π` of `l_K`. On pure tensors
  this is `B_T(w · χ|_T, γ) = B_T(χ|_T, w⁻¹ γ)` (`relativeWeylInvariantForm_invariant`).
* `linearIndependent_simpleRoots_real`, `one_tmul_notMem_span`: the simple roots are linearly
  independent in `X^*(T) ⊗ ℝ`, so a simple root outside `K` is not in the span of `K`.
* `restrict_simple_ne_zero`, `restrict_simple_mem_unipotentRoots`: for a simple `α ∉ K`,
  `α ∘ f_K` is a nonzero character of `A_K` and is a root of the presentation of `P_K` in its
  unipotent radical (`unipotentRoots`).
* `rootFunctional_neg`: the root form of `−γ ∘ f_J` is minus that of `γ ∘ f_J`.
* `exists_unipotentRoot_weylParameter`: let `(W, C)` be a Weyl conjugation from `P_I` to `P_K`
  with `W` a normalizer point whose action carries the simple roots of `I` into `K`, let `π` be a
  retraction of `l_K`, and let `α ∉ K` be simple. Then there is a root `β` of the presentation
  of `P_I` in its unipotent radical such that the vanishing of the root form of `β` at `ν`
  implies the vanishing of the root form of `α ∘ f_K` at `weylParameter l_I C π ν`. Proof:
  `g = W⁻¹ α` is a relative root (`relativeWeylLatticeAction_mapsTo_relativeRoots`), and
  `g ∘ f_I ≠ 0`, since otherwise `g` would lie in the span of `I` and `α = W g` in the span of
  `K`. Of `g` and `−g` (a root by `RelativeRootReflectionData.neg_mem_relativeRoots`) one is
  positive for the generic cocharacter; `β` is its composite with `f_I`, and
  `rootFunctional_weylParameter` and `rootFunctional_neg` transport the kernels.

## Provenance

Derived. Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`,
§8.6, pp. 225–226, supply the rank-one dependence of `M(s_α, λ)` on `⟨λ, α^∨⟩` and the
setting of root hyperplanes `⟨λ, β^∨⟩ = c`. The facts proved here are the linear algebra behind
that passage, for the root forms of the Library's `ParabolicRootPresentation` through the common
torus `T` and its Weyl-invariant form:

* the parameters on which the root form of `α` vanishes are restrictions of parameters of the
  larger parabolic (`exists_parameterRestrict_of_rootFunctional_eq_zero`, one inclusion);
* the root form of `α ∘ f_K` at the transported parameter equals the root form of the
  unsigned inverse-transported character `(W⁻¹ α) ∘ f_I` at the original parameter
  (`rootFunctional_weylParameter`);
* the root `β` of `P_I` is whichever of `W⁻¹ α` and `−W⁻¹ α` is positive; its root form is
  that form multiplied by the corresponding sign (`rootFunctional_neg`), so the two kernels
  agree, although the values differ by the sign when `W⁻¹ α` is negative.
