# Cones of Langlands' combinatorial lemma inside `𝔞*_∅` (definitions)

Module `Langlands.GroupScheme.Rational.LanglandsDecompositionCones`.
Namespace `Langlands.GroupScheme`. Universe parameter `u`.
The module contains six definitions and one membership lemma (proved by `simp`). It asserts
no structural theorem. Worker 24 wrote it under Task 5474
(`9abd0e5e-4606-4ee5-b449-49ac84438117`) for the statement module
`Langlands.GroupScheme.Rational.LanglandsDecompositionStatement` (Renard V.3.18).

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Worker 24 read
V.3.6–V.3.7 (printed p.111 / PDF p.117), V.3.12–V.3.18 (printed pp.112–115 /
PDF pp.118–121) and V.5.5 (printed pp.127–129 / PDF pp.133–135). The pages with cone closures
were checked as rendered images, because text extraction drops the bars.

The relevant source passages:

- V.3.7: "On supposera `𝔞_M` et `𝔞*_M` toujours munis de produits scalaires (notés `(.,.)`
  …) invariants sous l'action de `W(A_M)`." In the minimal case,
  `⟨α̌, λ⟩ = 2(α, λ)/(α, α)`.
- V.3.13: `𝔞_G ⊂ 𝔞_L ⊂ 𝔞_M ⊂ 𝔞_∅`, where `𝔞_M` is "l'orthogonal des racines
  `α ∈ Δ^M_∅`". The spaces `𝔞*_G ⊂ 𝔞*_L ⊂ 𝔞*_M ⊂ 𝔞*_∅` "sont décrits de la même manière en
  remplaçant les racines par les coracines". `(𝔞^G_∅)*` is spanned by the `α ∈ Δ_∅`, and
  `𝔞*_∅ = 𝔞*_G ⊕ (𝔞^G_∅)*`. "Ces décompositions sont orthogonales pour le produit scalaire
  fixé."
- V.3.14: `Δ(P) := {α|_{𝔞_M}, α ∈ Δ_∅ ∖ Δ^M_∅}`. For `β = α|_{𝔞_M}`, `β̌` is the projection
  of `α̌` onto `𝔞_M`.
- V.3.15: `⁺[𝔞*]^G_P = {Σ_{α ∈ Δ(P)} c_α α, c_α > 0}` and its closure has `c_α ≥ 0`;
  `^G_P[𝔞*]^+ = {χ ∈ 𝔞* | ⟨χ, α̌⟩ > 0, α ∈ Δ(P)}`, with the closure given by `≥ 0`.
- V.3.16: `^G_P[(𝔞^G_M)*]^+ = ^G_P[𝔞*_M]^+ ∩ (𝔞^G_M)* = {Σ_{α ∈ Δ(P)} c_α ϖ_α, c_α > 0}`
  is an open convex cone. Its closure has `c_α ≥ 0`. The closure decomposes cellularly over the
  standard `Q = LU ⊇ P` into the cones `^G_Q[(𝔞^G_L)*]^+`.
- V.3.17 proof: `^G_P[(𝔞^G_M)*]^+` "est l'ensemble
  `{x ∈ (𝔞^G_∅)* | α ∈ Δ^M_∅ ⇒ ⟨x, α̌⟩ = 0, α ∈ Δ_∅ ∖ Δ^M_∅ ⇒ ⟨x, α̌⟩ > 0}`".
- V.3.18, (V.3.18.1): `μ = μ_G + μ⁺ + μ⁻` "avec `μ_G ∈ 𝔞*_G`, `μ⁺ ∈ ^G_Q[(𝔞^G_L)*]^+` et
  `μ⁻ ∈ −p^L_M(closure of ⁺[𝔞*_M]^G_P)`".
- V.5.5, end of the proof: `μ⁺ = Σ_{i ∉ F(μ)} t_i ω_i` and `μ⁻ = −Σ_{j ∈ F(μ)} s_j α_j` with
  `t_i > 0`, `s_j ≥ 0`. Here the `α_j` are the elements of `Δ(P)`, and `Q` is the standard
  parabolic with `Δ(Q)` the restrictions of the `α_i`, `i ∉ F(μ)`.

Provenance: **source** for the first five definitions, which realize source objects. The
predicate `IsLanglandsDecomposition` follows the V.5.5 proof instead of the literal V.3.18
display. That is a **derived correction**, explained under "Source issue" below.

## Setting

The definitions take a field `k`, a commutative group scheme `T` and an actual monomorphism
`i : T → G` into an affine group scheme `G`. For the statement, `i` is a maximal split torus
(Renard's `A_∅`) of a connected reductive `G`. They also take a cocharacter `ν` of `T`, which
fixes the positive and simple relative roots `simpleRelativeRoots i ν` (Renard's `Δ_∅`, for the
generic `ν` of the statement). Finally they take `D : RelativeRootReflectionData i`. For every
relative root `α`, `D` supplies a cocharacter `D.coroot α` with `⟨α, D.coroot α⟩ = 2` and a
normalizer point that acts on characters by `χ ↦ χ − ⟨χ, D.coroot α⟩ α`. These are the coroots
`α̌`, as in the published `restrictedCorootChamber` and `CorootChamberUnipotentRootsStatement`.

`𝔞*_∅` is the published full real character space `RealTorusSpace.Vstar T = ℝ ⊗_ℤ X*(T)`. The
pairing `⟨x, α̌⟩` is `RealTorusSpace.pair T x (1 ⊗ D.coroot α)`. `1 ⊗ α` is the image of an
integral character in `Vstar T`. `relativeRootSpanReal i` is the real span of all actual
relative roots, i.e. Renard's `(𝔞^G_∅)*`. `rationalCharacterRestrictReal i` is the real scalar
extension of restriction of actual characters of `G` to `T`. Its range is Renard's `𝔞*_G`
inside `𝔞*_∅`: the published `RelativeCharacterRootComplementStatement` (proved) gives
`IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range` for connected
reductive `G`.

## Definitions

- `corootAnnihilator i D J : Submodule ℝ (Vstar T)` is the intersection, over the relative
  roots `α` with `α ∈ J`, of the kernels of `x ↦ ⟨x, α̌⟩`. The lemma `mem_corootAnnihilator`
  states the membership: `⟨y, α̌⟩ = 0` for every relative root `α ∈ J`. For `J = Δ^M_∅` this is
  Renard's `𝔞*_M ⊂ 𝔞*_∅` in the V.3.13 description (annihilator of the coroots of `M`).
- `openCorootFace i ν D K : Set (Vstar T)` is the set of `y ∈ relativeRootSpanReal i` with
  `⟨y, α̌⟩ = 0` for every relative root `α ∈ K` and `⟨y, α̌⟩ > 0` for every simple root
  `α ∉ K`. For `K = Δ^L_∅` this is exactly the V.3.17 display with `L` in place of `M`, i.e.
  `^G_Q[(𝔞^G_L)*]^+`.
- `closedCorootFace i ν D J : Set (Vstar T)` has the same conditions for `J`, with `≥ 0`
  instead of `> 0`. This is the closure of `^G_P[(𝔞^G_M)*]^+` in V.3.16:
  `{Σ_{Δ(P)} c_α ϖ_α, c_α ≥ 0}` in `(𝔞^G_M)*`. The coefficient of `ϖ_α` is `⟨y, α̌⟩`, because
  `y` kills the coroots of `J` and so `⟨y, β̌⟩ = ⟨y, α̌⟩` for `β = α|_{𝔞_M}`.
- `projectedRootNonnegCone i D J S : Set (Vstar T)` is the set of `y ∈ corootAnnihilator i D J`
  for which some `z` in the pointed cone generated by the vectors `1 ⊗ α`, `α ∈ S`, satisfies
  `y − z ∈ span_ℝ {1 ⊗ β : β ∈ J}`. The roots are restricted, not taken literally (see "Formal
  choices"), so this set is the closed cone `{Σ_{α ∈ S} c_α α|_{𝔞_M}, c_α ≥ 0}` of restricted
  roots, realized in `𝔞*_M ⊂ 𝔞*_∅`. For `S = Δ_∅ ∖ J` it is the closure of `⁺[𝔞*_M]^G_P`
  (V.3.15 with `𝔞 = 𝔞_M`). For `S = K ∖ J` with `J ⊆ K` it is the corresponding cone for the
  Levi `L` of `K`, which lies in `(𝔞^L_M)*`.
- `IsWeylInvariantInnerProduct i B` says that `B : LinearMap.BilinForm ℝ (Vstar T)` is
  symmetric, positive definite (`0 < B x x` for `x ≠ 0`) and invariant under the actual relative
  Weyl group `relativeWeylGroup i = N(k)/Z(k)`, acting on the full space through the published
  `relativeWeylFullRealAction i`. This is the V.3.7 hypothesis on the fixed inner product of
  `𝔞*_∅`. The products on the `𝔞*_M` are its restrictions, as in V.3.13.
- `IsLanglandsDecomposition i ν D J μ K μG μp μm` is the conjunction of: `J ⊆ K`,
  `K ⊆ simpleRelativeRoots i ν`, `μ = μG + μp + μm`, `μG ∈ (rationalCharacterRestrictReal i).range`
  (`μ_G ∈ 𝔞*_G`), `μp ∈ openCorootFace i ν D K` (`μ⁺ ∈ ^G_Q[(𝔞^G_L)*]^+`), and
  `−μm ∈ projectedRootNonnegCone i D J (K ∖ J)`. The last condition says that `μ⁻` is minus a
  nonnegative combination of the restrictions to `𝔞_M` of the simple roots in `K ∖ J`, as in
  the V.5.5 proof. The set `K` encodes the standard parabolic `Q = standardParabolic i ν K`,
  with Levi `L = standardLevi i ν K`. Containing `P` is `J ⊆ K`, by the published
  `StandardParabolicOrderStatement`.

## Formal choices

- **Realization in `𝔞*_∅`.** All cones are subsets of `Vstar T`, as in V.3.13, which places
  `𝔞*_M` inside `𝔞*_∅`. The definitions use only the actual character space of the maximal
  split torus. The statement module links `𝔞*_M ⊂ 𝔞*_∅` to the actual real character space of
  the split component `A_M`.
- **Restricted roots, not literal roots.** V.3.13 writes `(𝔞^L_M)*` as the span of the
  `α ∈ Δ^L_∅ ∖ Δ^M_∅` themselves. As recorded in source issue I4 of
  `notes/renard/item-ledger-v.md`, these roots need not lie in `𝔞*_M`. The definitions follow
  V.3.14 and use the restrictions `α|_{𝔞_M}`. Inside `𝔞*_∅`, `y ∈ 𝔞*_M` restricts to
  `α|_{𝔞_M}` exactly when `y − α` vanishes on `𝔞_M`. Here `𝔞_M` is the common kernel of the
  roots of `J`, so this condition is `y − α ∈ span(J)`. That is the definition of
  `projectedRootNonnegCone`. For a `W`-invariant product, `𝔞*_M` is the orthogonal complement
  of `span(J)`, so `y` is then the orthogonal projection of `α` to `𝔞*_M`. The definition
  itself needs no inner product.
- **Coroots from `D`.** The source defines `α̌` from the inner product (V.3.7). The Lean
  definitions use the coroots of the supplied integral reflection data. Agreement with
  `⟨α̌, λ⟩ = 2(α, λ)/(α, α)` for a `W`-invariant product is a consequence, not a hypothesis.
  It is listed as a proof obligation of the statement.
- **Ground field and generality.** The definitions make sense for any field and any actual
  monomorphism. Reductivity, maximal splitness and genericity are hypotheses of the
  statement.

## Source issue in V.3.18 (the `μ⁻` cone)

Read literally, the condition `μ⁻ ∈ −p^L_M(closure of ⁺[𝔞*_M]^G_P)` is too weak for the
asserted uniqueness. `p^L_M` is the orthogonal projection of `𝔞*_M` onto `(𝔞^L_M)*`, and it
can send restricted roots outside `L` to negative multiples of roots of `L`. Then the
projected cone becomes a whole subspace.

Example: `A_2`, `J = ∅` (`P = P_∅`), `(α_i, α_i) = 2`, `(α_1, α_2) = −1`, and
`μ = 2ϖ_1 = ϖ_2 + α_1`.

- `K = {α_2}` gives `μ⁺ = 2ϖ_1` and `μ⁻ = 0`.
- `K = {α_1}` gives `μ⁺ = ϖ_2 ∈ ^G_Q[(𝔞^G_L)*]^+`. Here `p^L_M(α_1) = α_1` and
  `p^L_M(α_2) = −α_1/2`, so `−p^L_M(closure of ⁺[𝔞*_∅]^G_{P_∅}) = ℝα_1 ∋ α_1 = μ⁻`.

Both satisfy the literal (V.3.18.1). In the second, `μ⁺` is not the projection of `μ` onto the
closed cone. The V.5.5 proof produces `μ⁻ = −Σ_{j ∈ F(μ)} s_j α_j` with `s_j ≥ 0` and `α_j`
the restrictions to `𝔞_M` of the roots of `K ∖ J`. That is the condition used here. It is the
closed cone of V.3.15 for the Levi `L` (the `G`-cone `closure of ⁺[𝔞*_M]^G_P` intersected with
`(𝔞^L_M)*`), and it gives uniqueness. The projection characterizations of V.3.18 are stated
unchanged in the statement module.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.RelativeCentralDirections` | `relativeWeylFullRealAction`, `relativeRootSpanReal`, `rationalCharacterRestrictReal`, and through it `RealTorusSpace.Vstar`, `RealTorusSpace.pair`, `relativeRoots`, `relativeWeylGroup` |
| `Langlands.GroupScheme.Rational.RootReflectionAssembly` | `RelativeRootReflectionData` |
| `Langlands.GroupScheme.Rational.StandardParabolic` | `simpleRelativeRoots` |
| `Mathlib.Geometry.Convex.Cone.Pointed` | `PointedCone.hull` |
| `Mathlib.LinearAlgebra.BilinearForm.Basic` | `LinearMap.BilinForm` |
