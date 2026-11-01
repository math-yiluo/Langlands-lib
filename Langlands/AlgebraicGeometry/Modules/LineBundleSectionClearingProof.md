# Proof of line-bundle scalar section clearing

`Langlands.SchemeModule.lineBundleSectionClearing` proves the published
proposition `Langlands.SchemeModule.LineBundleSectionClearingStatement.{u}`
from module `Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingStatement`.
The theorem's type is that proposition itself, in an arbitrary universe `u`,
with no further hypotheses. The statement pair and everything it imports are
unchanged.

Let `X` be quasi-compact and quasi-separated, `L : LineBundle X`,
`s : GlobalSections L.obj`, `U = trivializationOpen L.obj s`, and
`r : Γ(X, U)`. The proof produces `m` and a global section `a` of the actual
right-associated `tensorPow L.obj m` such that `a` restricted to `U` equals
`r • (sectionPow L.obj s m restricted to U)`. The restriction maps are the
exact maps in the statement. No hypothesis excludes zero sections, zero
functions, empty opens or the empty scheme. The exponent produced may be zero.

All helper declarations are in namespace
`Langlands.SchemeModule.SectionClearing`. The module sets
`backward.isDefEq.respectTransparency false`, as the Library module
`Picard.AffineGenerationLocusIntersectionProof` does.

## Overview

The proof follows the corrected route of Stacks tag 01PW, part (2), with the
correction recorded in that page's comments. It covers `X` by finitely many
affine opens on which `L` is trivial. On each affine open, `U` is a basic open.
It clears the denominators of `r` there with one common exponent, then kills
the finitely many overlap differences with a further common power of `s`, and
glues. The Lean proof has three parts.

1. **Multiplication by `s`.** A module morphism
   `sectionMulPow L s m : tensorPow L m ⟶ tensorPow L (m + 1)` sends
   `sectionPow L s m` to `sectionPow L s (m + 1)`.
2. **Abstract gluing.** For any sequence of module sheaves `N m` with
   morphisms `μ m : N m ⟶ N (m + 1)`, global sections `p m` with
   `μ m (p m) = p (m + 1)`, and an open `U`, the clearing conclusion follows
   if every point has a *local chart* (defined below). This part uses only
   sheaf gluing, quasi-compactness and quasi-separatedness.
3. **Charts from trivializations.** A trivialization of `L` on an open `T`
   gives a local chart for `N m = tensorPow L m` and `μ m = sectionMulPow L s m`
   on `T`. Its multiplier `c` satisfies `X.basicOpen c = T ⊓ U`.

## Part 1: multiplication by `s`

`sectionMul L s N` is the composite
`(tensorLeftUnitor N).inv ≫ tensorMap (sectionHom L s) (𝟙 N) : N ⟶ L ⊗ N`.
`sectionMulPow L s m` is `sectionMul L s (tensorPow L m)`, typed with target
`tensorPow L (m + 1)`, which is definitionally `tensorObj L (tensorPow L m)`.

The proof uses `Langlands.Scheme.Modules.tensorLeftUnitor_inv_naturality` from
[RigidifiedInverse](../Picard/RigidifiedInverse.md), reversing its equality when needed:
`f ≫ (tensorLeftUnitor N).inv = (tensorLeftUnitor M).inv ≫ tensorMap (𝟙 _) f`.

`sectionMul_app_sectionPow` proves
`(sectionMul L s (tensorPow L m)).app ⊤ (sectionPow L s m) = sectionPow L s (m + 1)`.
Global sections are determined by their section morphisms
(`sectionHom_injective`). By `sectionHom_naturality`, `sectionPow_succ` and
`sectionHom_tensorSection`, both sides become morphisms out of the structure
module. Inverse unitor naturality and `tensorMap_comp` make them equal:
`p ≫ λ⁻¹ ≫ (σ ⊗ 1) = λ⁻¹ ≫ (1 ⊗ p) ≫ (σ ⊗ 1) = λ⁻¹ ≫ (σ ⊗ p)`.

## Restriction bookkeeping

`presheaf_map_map`, `presheaf_map_id`, `modules_map_map` and `modules_map_id`
compose restriction maps along `homOfLE` for functions and for module
sections. `hom_app_map` states that module morphisms commute with
restriction.

## Part 2: gluing from local charts

Fix `N : ℕ → X.Modules` and `μ : ∀ m, N m ⟶ N (m + 1)`.

- `powMul N μ n k : N n ⟶ N (n + k)` is the `k`-fold composite of the `μ`
  (`𝟙` for `k = 0`, then `powMul n k ≫ μ (n + k)`).
- `powMul_app_top`: if `μ m (p m) = p (m + 1)` for all `m`, then
  `powMul n k` sends `p n` to `p (n + k)`.
- `powMul_app_eq_zero_of_le`: if `powMul n k₀` kills a section, so does
  `powMul n k` for every `k ≥ k₀`, because each `μ` maps zero to zero.
- `powMul_good`: if `b ∈ Γ(N n, V)` satisfies
  `b|_{V ⊓ U} = r|_{V ⊓ U} • p n|_{V ⊓ U}`, then `powMul n k` applied to `b`
  satisfies the same identity with `p (n + k)`. The proof uses naturality,
  linearity (`Hom.app_smul`) and `powMul_app_top`.

A `LocalChart N μ T c`, for an open `T` and `c : Γ(X, T)`, consists of maps
`E m W hW : Γ(N m, W) → Γ(X, W)` for every `m` and every open `W ≤ T`. The
following hold.

- Each `E m W hW` is injective and surjective.
- `E` commutes with restriction (`res`).
- `E (t • d) = t * E d` for `t : Γ(X, W)` (`smul`).
- `E (m + 1) W hW (μ m d) = E m W hW d * c|_W` (`mul`).

Consequences, in namespace `LocalChart`:

- `E_zero`: `E` sends zero to zero, by `smul` with `t = 0`.
- `E_powMul`: `E (n + k) (powMul n k d) = E n d * (c|_W) ^ k`, by induction
  on `k`.
- `E_pow`: `E m (p m|_W) = E 0 (p 0|_W) * (c|_W) ^ m`, by induction on `m`
  using `μ m (p m) = p (m + 1)` and naturality.
- `exists_powMul_eq_zero` (kernel step): assume `X.basicOpen c = T ⊓ U`,
  `W ≤ T` with `W` quasi-compact, and `d ∈ Γ(N n, W)` with `d|_{W ⊓ U} = 0`.
  Then some `powMul n k` kills `d`. By `Scheme.basicOpen_res`, the basic open
  of `f = c|_W` is `W ⊓ U`. The coordinate `E n d` restricts to zero on
  `X.basicOpen f`, because `E` commutes with restriction and `E_zero` holds.
  Mathlib's `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact`
  gives `f ^ k * E n d = 0`. By `E_powMul` this is the coordinate of
  `powMul n k d`, and injectivity finishes the step.
- `exists_local` (local existence): for an affine open `V ≤ T`, there are `n`
  and `b ∈ Γ(N n, V)` with `b|_{V ⊓ U} = r|_{V ⊓ U} • p n|_{V ⊓ U}`. With
  `f = c|_V` and `X.basicOpen f = V ⊓ U`, Mathlib's
  `exists_eq_pow_mul_of_isAffineOpen` gives `n` and `y : Γ(X, V)` with
  `y|_{D(f)} = (f|_{D(f)}) ^ n * r|_{D(f)}`. Restricting along
  `V ⊓ U ≤ D(f)` gives `y|_{V ⊓ U} = (c|_{V ⊓ U}) ^ n * r|_{V ⊓ U}`. Let `b`
  be the section with coordinate `y * E 0 (p 0|_V)`, by surjectivity. Then
  `E_pow`, `smul` and `res` show that both sides of the claim have coordinate
  `y|_{V ⊓ U} * E 0 (p 0|_V)|_{V ⊓ U}` on `V ⊓ U`. Injectivity gives the
  claim. Multiplying by `E 0 (p 0|_V)` absorbs the coordinate of the unit
  section, so no condition on `E 0` is needed.

`exists_global_of_charts` assumes `CompactSpace X` and
`QuasiSeparatedSpace X`, `μ m (p m) = p (m + 1)` for all `m`, and charts:
every point `x` lies in an open `T` with some `c : Γ(X, T)` such that
`X.basicOpen c = T ⊓ U` and there is a `LocalChart N μ T c`. It concludes the
clearing statement for every `r : Γ(X, U)`, with `a : Γ(N m, ⊤)`. The proof
runs as follows.

1. For each point choose a chart open `T x` and an affine open `V x` with
   `x ∈ V x ≤ T x` (`isBasis_affineOpens`). Compactness of `X`
   (`isCompact_univ.elim_finite_subcover`) gives a finite set `t` of points
   whose `V` cover `X`.
2. By `exists_local` and `powMul_good`, for each `i ∈ t`, local solutions on
   `V i` exist for all sufficiently large exponents. `Filter.eventually_all`
   over the finite index set gives one exponent `e` and solutions
   `b i ∈ Γ(N e, V i)`. This is the common-exponent correction of the Stacks
   proof.
3. For each pair `(i, j)`, the overlap difference
   `b i|_{V i ⊓ V j} - b j|_{V i ⊓ V j}` vanishes on `V i ⊓ V j ⊓ U`. Both
   restrict there to `r • p e`. The overlap is quasi-compact by
   quasi-separatedness (`IsCompact.inter_of_isOpen` for the affine, hence
   compact, opens), and it lies in `T i`. So `exists_powMul_eq_zero` kills
   it by some power, and `powMul_app_eq_zero_of_le` gives all larger powers.
   `Filter.eventually_all` over the finite set of pairs gives one `k`.
4. The sections `powMul e k (b i)` are compatible on overlaps, by naturality
   and additivity. `TopCat.Sheaf.existsUnique_gluing'` for the sheaf
   `(N (e + k)).presheaf` glues them to `a ∈ Γ(N (e + k), ⊤)`.
5. `TopCat.Sheaf.eq_of_locally_eq'` on the cover `V i ⊓ U` of `U` proves
   `a|_U = r • p (e + k)|_U`. On each `V i ⊓ U`, the left side is
   `powMul e k (b i)` restricted, and `powMul_good` computes it.

## Part 3: charts from trivializations

### Generic chart from compatible trivializations

Fix an open `T` of `X`. Typed identity casts mediate between definitionally
equal section types. `toT`/`ofT` relate sections of `structureSheaf Y` to
functions. `ofImage`/`toImage` relate sections of `M.restrict T.ι` over `W'`
to sections of `M` over `T.ι ''ᵁ W'`. Their rewriting lemmas (`toT_smul`,
`toT_map`, `ofImage_map`, `ofImage_app`, ...) are proved by `rfl`, except
for the following:

- `toT_app`: an endomorphism `φ` of the structure module multiplies by
  `unitEndCoefficient φ ⊤` restricted. This is the Library's
  `unitEndCoefficient_app` and `unitEndCoefficient_res`.
- `ofImage_smul`: the action of `t : Γ(X, T.ι ''ᵁ W')` on `M` is the action
  of `(T.ι.appIso W').hom t` on the restriction (`Iso.hom_inv_id_apply`).
- `appIso_inv_res`: the inverse of `T.ι.appIso` commutes with restriction
  (`Scheme.Hom.appIso_inv_naturality`).

For `Ψ : M.restrict T.ι ≅ structureSheaf T` and `W ≤ T`, put
`W' = T.ι ⁻¹ᵁ W`. Then `T.ι ''ᵁ W' ≤ W` (`image_preimage_le`) and
`W ≤ T.ι ''ᵁ W'` (`le_image_preimage`). `chartE Ψ W hW d` restricts `d` to
`T.ι ''ᵁ W'`, applies `Ψ.hom` over `W'`, transports by
`(T.ι.appIso W').inv`, and restricts back to `W`. `chartF` does the same with
`Ψ.inv` and `appIso.hom` in the opposite direction. The two restriction maps
in each composite cancel because they compose to identity maps.

- `chartE_chartF` and `chartF_chartE` show they are mutually inverse.
- `chartE_res`: compatibility with restriction, from naturality of `Ψ.hom`
  and `appIso_inv_res`.
- `chartE_smul`: linearity, from `map_smul`, `ofImage_smul`, `Hom.app_smul`
  and multiplicativity of `appIso.inv`.

Now let `Ψ m : (N m).restrict T.ι ≅ structureSheaf T` for every `m` and
`φ : structureSheaf T ⟶ structureSheaf T`, with
`restrictFunctor.map (μ m) ≫ (Ψ (m + 1)).hom = (Ψ m).hom ≫ φ`. Define
`chartCoeff φ : Γ(X, T)` as the transport of `unitEndCoefficient φ ⊤` along
`(T.ι.appIso ⊤).inv` and restriction along `T ≤ T.ι ''ᵁ ⊤`. `chartCoeff_eq`
identifies it with `T.topIso.hom (unitEndCoefficient φ ⊤)`. `chartE_mul`
proves the `mul` axiom with `c = chartCoeff φ`, using the compatibility,
`toT_app` and `appIso_inv_res`. `localChartOf` assembles the `LocalChart`.

### Compatible trivializations of the tensor powers

Let `e : L.restrict T.ι ≅ SheafOfModules.unit T.ringCatSheaf`. Pullback
`P = Scheme.Modules.pullback T.ι` is used for the tensor comparison. Its
Library comparison `pullbackTensorComparisonApp` is natural
(`pullbackTensorComparisonApp_naturality`), invertible
(`pullbackTensorComparisonIsIso`; `pullbackTensorIso` is the resulting
isomorphism), and compatible with the left unitor
(`pullbackTensorLeftUnitor`, together with `pullbackUnitIso`). Mathlib's
`restrictFunctorIsoPullback T.ι` relates restriction and pullback.

- `pullbackTriv`: the trivialization `P L ≅ 𝒪_T` from `e`.
- `chartMulOf σ` is `(pullbackUnitIso T.ι).inv ≫ P.map σ ≫ pullbackTriv.hom`
  for `σ : 𝒪_X ⟶ L`.
- `powTriv m : P (tensorPow L m) ≅ 𝒪_T` is `pullbackUnitIso` for `m = 0`.
  For `m + 1` it is the tensor comparison, followed by tensoring
  `pullbackTriv` with `powTriv m`, followed by the left unitor of `𝒪_T`.
- `pullback_mul_comp`: for any `Θ : P N ≅ 𝒪_T`, the pullback of
  `(tensorLeftUnitor N).inv ≫ tensorMap σ (𝟙 N)`, followed by the
  `m + 1`-step of `powTriv` built from `Θ`, equals `Θ.hom ≫ chartMulOf σ`.
  The proof uses the following, in order: comparison naturality; the
  pullback left-unitor law, inverted to
  `P(λ⁻¹) ≫ c = λ⁻¹ ≫ (pullbackUnitIso.inv ⊗ 1)`; `tensorMap_comp`;
  inverse left-unitor naturality; `tensorUnitors_equal` on `𝒪_T`; and
  `tensorRightUnitor_naturality`.
- `chartIso m = (restrictFunctorIsoPullback T.ι).app _ ≪≫ powTriv m` and
  `chartIso_succ` gives the compatibility required by `localChartOf`, with
  `φ = chartMulOf (sectionHom L s)`. It uses naturality of
  `restrictFunctorIsoPullback`.

### The multiplier cuts out the generation open

`basicOpen_chartCoeff` proves
`X.basicOpen (chartCoeff (chartMulOf T L.obj e (sectionHom L.obj s))) = T ⊓ trivializationOpen L.obj s`.
It follows the proof of the Library's
`exists_inf_trivializationOpen_eq_basicOpen`. By naturality of
`restrictFunctorIsoPullback`, `chartMulOf` equals an isomorphism, followed by
`restrictFunctor.map (sectionHom L.obj s)`, followed by `e.hom`. So its stalk
at `y` is invertible exactly when `IsStalkFrame L.obj s (T.ι y)` holds
(`isIso_stalk_restrict_iff`). The published `lineBundle_stalkFrame_set_eq`
identifies stalk-frame points with `trivializationOpen L.obj s`.
`unitEnd_stalkIso_iff_mem_basicOpen` identifies stalk-isomorphism points with
the basic open of the coefficient. `chartCoeff_eq` and
`Scheme.Opens.ι_image_basicOpen_topIso_inv` move that basic open into `X`.

## Final assembly

`lineBundleSectionClearing` applies `exists_global_of_charts` with
`N = tensorPow L.obj`, `μ = sectionMulPow L.obj s`, `p = sectionPow L.obj s`
and `sectionMul_app_sectionPow`. For each point `x`, the `LineBundle`
property gives an open `T ∋ x` and a trivialization `e`. The chart is
`localChartOf (chartIso T L.obj e ·) _ (chartIso_succ T L.obj e s)`, and its
basic-open condition is `basicOpen_chartCoeff`.

No `sorry`, `admit` or new axiom is used. The theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The mathematical source is Stacks Project tag 01PW, part (2) (Properties of
Schemes, Lemma 28.18.2). It is retained in the registered snapshot
`stacks-section-open-prerequisites-2026-10-29` (`01PW.html`), including the
correction in comments #4719 and #4809. That correction takes a common
exponent before gluing and then clears the overlap differences by a further
common power. The Lean proof implements that corrected argument for the
structure sheaf. It replaces local frames by the explicit pullback-tensor
trivializations above. It uses quasi-compactness only for the finite affine
cover, and quasi-separatedness only for quasi-compactness of overlaps.
