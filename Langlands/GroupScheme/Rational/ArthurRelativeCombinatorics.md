# Arthur's parabolic combinatorics for an actual reductive group

Module `Langlands.GroupScheme.Rational.ArthurRelativeCombinatorics`, namespace
`Langlands.GroupScheme.ArthurRelative`. Worker 128, Task 5536, item 1 (the specialization of the
abstract layer to actual groups).

The published abstract layer `Langlands.ArthurCombinatorics` (modules
`Langlands/LinearAlgebra/ArthurCombinatorics` and `ArthurCombinatoricsStatement`) defines
Arthur's spaces, weights and characteristic functions for a real root system with a Mathlib
`RootPairing.Base`. This module supplies that input for the relative root system of an actual
connected reductive group, and pulls the abstract functions back to the actual space `𝔞_0`. It
proves that the pulled-back objects satisfy Arthur's defining properties. All proofs in the module
are complete. It states no new proposition.

## Sources

- J. Arthur, *A trace formula for reductive groups I: terms associated to classes in G(ℚ)*, Duke
  Math. J. 45 (1978), registered as `arthur-1978-trace-formula-reductive-groups-I`, §1,
  pp.915–916 (PDF pages 5–6). `Δ_0 = Δ_{P_0}` "is a base for a root system", with coroots
  `α^∨ ∈ 𝔞_0`. For `P_1 ⊆ P_2`, `P_2 ↦ Δ_{P_1}^{P_2}` is a bijection from parabolics containing
  `P_1` onto subsets of `Δ_{P_1}`, and `𝔞_{P_2} = {H ∈ 𝔞_{P_1} : α(H) = 0, α ∈ Δ_{P_1}^{P_2}}`.
  Each `α ∈ Δ_{P_1}^{P_2}` is the restriction of a unique `β ∈ Δ_0^{P_2}`, and `α^∨` is the
  projection onto `𝔞_{P_1}` of `β^∨`. §6, pp.938–940, defines `τ`, `τ̂`, `σ`, `ε` and `φ`.
- J. Arthur, *An introduction to the trace formula* (2005), in the volume registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12):
  - §5, pp.24–26. The split exact sequences giving `𝔞_{P_1} = 𝔞_{P_2} ⊕ 𝔞_{P_1}^{P_2}`. The pair
    `((𝔞_{P_0}^G)^*, Φ_0 ∪ −Φ_0)` is called a root system, with simple roots `Δ_0`; `Δ_0` is a
    basis of `(𝔞_0^G)^*` and `Δ_0^∨` a basis of `𝔞_0^G`; `Δ̂_0` is the basis dual to `Δ_0^∨`.
    Standard parabolics correspond to subsets `Δ_0^P ⊆ Δ_0`, with
    `𝔞_P = {H ∈ 𝔞_0 : α(H) = 0, α ∈ Δ_0^P}`; `Δ̂_P = {ϖ_α : α ∈ Δ_0 − Δ_0^P}`; for `α ∈ Δ_P` the
    restriction of `β`, `α^∨` is the projection of `β^∨` onto `𝔞_P`; `Δ̂_{P_1}^{P_2}` is obtained
    by restricting the elements of `Δ̂_{P_1} − Δ̂_{P_2}` to `𝔞_{P_1}^{P_2}`.
  - §8, pp.39–42, the functions `τ_{P_1}^{P_2}`, `τ̂_{P_1}^{P_2}` and `σ_{P_1}^{P_2}` regarded as
    functions on `𝔞_0`, through `𝔞_0 = 𝔞_0^{P_1} ⊕ 𝔞_{P_1}^{P_2} ⊕ 𝔞_{P_2}`.

Arthur works over `ℚ` (and in Part II over a number field). The constructions here are linear
algebra on the actual torus spaces and are stated over every field `k`, as the published Renard
V.3 linear algebra is (`RelativeRealCorootStatements`).

## Setting

- `k : Type u` a field, `G` a group scheme over `Spec k` with `hG : IsConnectedReductive G`, and
  `i : T.toGrp ⟶ G` with `hi : IsMaximalSplitTorus i`; `T` is Arthur's `A_0`. The instance
  arguments `[IsAffineHom G.X.hom]` and `[Mono i.hom.hom.left]` are those of the published
  relative-root API; they are propositions, so any instances (for example those derived from
  `hG` and `hi`) give the same objects.
- `ν : cocharacterLattice T` a cocharacter, with `hν : IsGenericCocharacter i ν` wherever the
  base is used. It fixes the minimal parabolic `P_0`: `Δ_0 = simpleRelativeRoots i ν`.
- `D : RelativeRootReflectionData i`, published integral reflection data. The coroots do not
  depend on `D` (published `RelativeRealCorootStatement`, proved), and such `D` exists
  (`relativeRootReflectionExistence`).
- `𝔞_0 = V T = ℝ ⊗ X_*(T)` and `𝔞_0^* = Vstar T = ℝ ⊗ X^*(T)`, with the pairing `pair T`
  (module `RealTorusSpace`). The comparison of `𝔞_0` with Arthur's `Hom(X(M_0)_F, ℝ)` and of
  `𝔞_P` with `Hom(X(M_P)_F, ℝ)` (`RealCharacterDual F P`) is not part of this module.
- A standard parabolic subgroup `P` is recorded by `J = Δ_0^P`, a set of characters contained in
  `Δ_0`. The published `StandardParabolicClassificationStatement` (Borel–Tits §5.14), proved by
  `standardParabolicClassification`, says that the dynamic rational parabolics containing `P_0`
  are the standard functors `standardParabolic i ν J`, `J ⊆ Δ_0`, and that every rational parabolic
  is rationally conjugate to the standard functor of exactly one `J ⊆ Δ_0`. `standardIndex_injOn` and `standardIndex_image` show that `J ↦ Θ`
  below is a bijection from subsets of `Δ_0` onto subsets of the base.

## Definitions

- `rootPairing hG hi D` is the published
  `RelativeRootReflectionData.indivisibleRealRootPairing`. It is indexed by the indivisible
  relative roots `RelativeRoot.indivisibleRoots i`, lives on `(𝔞_0^G)^* = relativeRootSpanReal i`
  and `𝔞_0^G = D.realCorootSpan`, has roots `1 ⊗ α` (`rootPairing_root`), coroots
  `D.realCoroot α` (`rootPairing_coroot`) and pairing `pair T` (`rootPairing_toLinearMap`). The
  published hypotheses are filled from `hG` and `hi`. Among them is a `W`-invariant inner product,
  chosen with `Classical.choose`; it only proves that the pairing is perfect, so no data depends on
  the choice. Instances: `IsRootSystem`, `IsCrystallographic`, and `IsReduced` (from
  `RootPairing.isReduced_of_no_double`).
- `simpleIndex ν` is `Δ_0` as a set of indices. `simpleRelativeRoots_subset_indivisibleRoots`
  shows that simple roots are indivisible: if `α = m β`, `m > 1`, then `m = 2` by the published
  multiplicity bound and `α = β + β` is a sum of positive roots.
- `base hG hi hν D` is the Mathlib base `RootPairing.Base.mk'` with support `simpleIndex ν`
  (`mem_support_base`). Its two inputs are `linearIndepOn_simpleIndex` (from the published real
  linear independence `linearIndependent_realSimpleRoots`) and `root_mem_closure_simpleIndex`:
  each indivisible root is a nonnegative or nonpositive integral combination of `Δ_0`. The second
  uses the genericity of `ν` (every root is positive or negative), negation of roots, and the
  published `DominantDisplacement.positive_mem_closure`. Mathlib derives the coroot axioms.
- `standardIndex hG hi ν J` is `Θ = {α : α ∈ Δ_0, α ∈ J}`, a finite set of indices
  (`mem_standardIndex`), with `standardIndex_mono`, `standardIndex_subset_support`,
  `standardIndex_simpleRelativeRoots` (`Θ = Δ_0` for `J = Δ_0`), `standardIndex_image` and
  `standardIndex_injOn`.
- `toCorootSpan hG hi D : 𝔞_0 → 𝔞_0^G` is the projection along `𝔞_G = relativeCentralDirections i`
  for `𝔞_0 = 𝔞_G ⊕ 𝔞_0^G` (`isCompl_relativeCentralDirections`, the published
  `central_isCompl_realCorootSpan`). `toRootSpan hG hi : 𝔞_0^* → (𝔞_0^G)^*` is the projection along
  `𝔞_G^*`, the real restricted rational characters of `G` (`isCompl_relativeRootSpanReal`, the
  published `relativeCharacterRootComplement`). Lemmas: `toCorootSpan_apply_coe`,
  `toCorootSpan_apply_eq_zero_iff`, `sub_toCorootSpan_mem`, `toRootSpan_apply_coe`,
  `sub_toRootSpan_mem`, and `pair_toRootSpan` (a vector of `𝔞_0^*` and its projection pair equally
  with `𝔞_0^G`).
- The pulled-back functions, for `J, J₁, J₂, JQ, JP` sets of simple roots:
  - `weight … J β : 𝔞_0 → ℝ` is `weightCoordinate (rootPairing) Θ ⟨β, _⟩ ∘ toCorootSpan` for an
    indivisible root `β`, and `0` otherwise;
  - `levelProjection … J = id − ∑_{β ∈ Θ} weight(·) β^∨`, Arthur's `H ↦ H_P` on `𝔞_0`;
  - `tau … J₁ J₂ H` and `tauHat … J₁ J₂ H` are `τ_{P_1}^{P_2}(H)` and `τ̂_{P_1}^{P_2}(H)`;
  - `sigma … J₁ J₂ H` is `σ_{P_1}^{P_2}(H)`, the abstract `sigma` with `G` given by `Δ_0`;
  - `epsilon … JQ JP Λ` and `phi … JQ JP Λ H` are `ε_Q^P(Λ)` and `φ_Q^P(Λ, H)` for `Λ ∈ 𝔞_0^*`.

  Each is the abstract function of the index sets `Θ`, evaluated at `toCorootSpan H` and
  `toRootSpan Λ`. The functions are integer valued, as in the abstract layer.
- `aSpace T J = rootAnnihilator T J` is `𝔞_P` (Arthur 2005, p.26), `corootSubspace D J` is
  `𝔞_0^P`, the span of the coroots of `J`, and `relativeSpace D J K` is `𝔞_P^Q`, the published
  `leviCorootSpace J K` (the part of `𝔞_P` in the span of the coroots of `K`).

## Arthur's definitions: what is proved

Throughout, `J` (resp. `J₂`, `K`) is contained in `Δ_0`.

- `levelProjection_eq_projectionOnto`: `levelProjection … J` is the projection of
  `𝔞_0 = 𝔞_0^P ⊕ 𝔞_P` onto `𝔞_P`, that is, Arthur's `H ↦ H_P`. It rests on
  `levelProjection_mem_rootAnnihilator` (`H_P ∈ 𝔞_P`) and `sub_levelProjection_mem_span`
  (`H − H_P ∈ 𝔞_0^P`). `levelProjection_eq` writes `H_P` as the `𝔞_G`-part of `H` plus the
  abstract level projection of its `𝔞_0^G`-part.
- `weight_coroot`: `ϖ_β(α^∨) = δ_{βα}` for `α, β ∈ J`; `weight_eq_zero_of_mem_rootAnnihilator`:
  the weights vanish on `𝔞_P`. So `weight … J β (H)` is the coefficient of `β^∨` in the
  `𝔞_0^P`-component of `H`. `weight_eq_of_mem_corootSubspace`: on `𝔞_0^P` the weight of `P` equals
  the weight of any `Q ⊇ P`, in particular the weight `ϖ_β ∈ Δ̂_0` of `G`. Together these give
  Arthur's description of `Δ̂_{P_1}^{P_2}`: the weight of `P_2` attached to `β ∈ Δ_0^{P_2} − Δ_0^{P_1}`
  vanishes on `𝔞_0^{P_1}` (by `weight_coroot`) and on `𝔞_{P_2}`, and on `𝔞_{P_1}^{P_2} ⊆ 𝔞_0^{P_2}`
  it is the restriction of `ϖ_β ∈ Δ̂_{P_1} − Δ̂_{P_2}`. For `J₂ = Δ_0` it is the weight `ϖ_β` of
  `G` evaluated on `𝔞_0` through `𝔞_0 → 𝔞_0^G`.
- `tau_eq`: `τ_{P_1}^{P_2}(H) = 1` iff `β(H_{P_1}) > 0` for all `β ∈ J₂ − J₁`. The roots of
  `Δ_{P_1}^{P_2}` are the restrictions of these `β` to `𝔞_{P_1}`, so this is Arthur's definition.
- `tauHat_eq`: `τ̂_{P_1}^{P_2}(H) = 1` iff `ϖ_β(H) > 0` for all `β ∈ J₂ − J₁`, with
  `ϖ_β = weight … J₂ β`.
- `corootValue_eq`: the abstract `Λ(α^∨)` equals `pair T Λ (H_Q)` for `H = β^∨`, the projection to
  `𝔞_Q` of the coroot `β^∨`; this is Arthur's `α^∨`. `epsilon_eq` and `phi_eq` restate
  `ε_Q^P(Λ)` and `φ_Q^P(Λ, H)` with this value and with `weight … JP`.
- `sigma` is Arthur's formula by definition: the abstract sum over `Θ₂ ⊆ Θ₃ ⊆ Δ_0` is the sum over
  standard `P_3 ⊇ P_2`, with the abstract layer's sign `(−1)^{|Θ₃ − Θ₂|}` for Arthur's
  `(−1)^{dim(A_{P_2}/A_{P_3})}`. (The dimension count `dim 𝔞_{P_2} − dim 𝔞_{P_3} = |Θ₃ − Θ₂|`
  follows from the decompositions above and the linear independence of the simple coroots; it is
  not restated as a theorem here.)
- Spaces: `aSpace_simpleRelativeRoots` (`𝔞_G` is `𝔞_P` for `P = G`),
  `isCompl_corootSubspace_aSpace` (`𝔞_0 = 𝔞_0^P ⊕ 𝔞_P`), `disjoint_aSpace_relativeSpace` and
  `aSpace_sup_relativeSpace` (`𝔞_P = 𝔞_P^Q ⊕ 𝔞_Q` for `P ⊆ Q`). Together they give
  `𝔞_0 = 𝔞_0^P ⊕ 𝔞_P^Q ⊕ 𝔞_Q`; with `Q = G` (`K = Δ_0`) the second is `𝔞_P = 𝔞_P^G ⊕ 𝔞_G`, by
  `aSpace_simpleRelativeRoots`. This includes the central part `𝔞_G` that the abstract layer
  omits. These theorems are the published Renard V.3.13 decomposition
  `standardLeviRealDecomposition`, restated in Arthur's notation.

The published abstract statements (`ArthurCombinatoricsStatement`, proved by
`arthurCombinatoricsStatement`) can be instantiated with `rootPairing hG hi D` and
`base hG hi hν D`. Since each function here is by definition the abstract function of the index
sets at `toCorootSpan H` or `toRootSpan Λ`, the instances are Arthur 1978 Proposition 1.1,
Lemmas 6.1 and 6.3 and Arthur 2005 (8.2) and Lemma 8.3 for these functions of the actual group.
This module does not restate those instances as separate theorems.

## Non-reduced relative root systems

A Mathlib base excludes non-reduced systems (type `BC`). The base here is a base of the reduced
system of indivisible roots. Arthur uses only `Δ_0` and the coroots of its elements, and `Δ_0`
consists of indivisible roots (`simpleRelativeRoots_subset_indivisibleRoots`), so nothing is lost.
The divisible roots `2α` of a `BC` system and their coroots `α^∨/2` do not occur.

## Scope

- Not done here: the comparison of `𝔞_P = aSpace T J` with `RealCharacterDual F P` (the target of
  `IsIwasawaCompact.height`) and of `𝔞_P^*` with `RealCharacterParameter F P` for the standard
  parabolic subgroup schemes, the `(G, M)`-families and the truncation operator. These are later
  units of Task 5536.
- The functions are defined for every set `J` of characters. Outside `J ⊆ Δ_0` they are formulas
  without meaning: `standardIndex` intersects with `Δ_0`. The theorems assume the intended range.

## Provenance

The objects are Arthur's (source). The base construction, the projections along the published
complements and the identification lemmas are derived: they are standard consequences of the
published relative root system, its real coroots and the Renard V.3 decompositions, proved here.
