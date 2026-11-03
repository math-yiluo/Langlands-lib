# Kaletha–Prasad affine root systems: hyperplanes, special points and facets

Module `Langlands.Geometry.Building.AffineRootSystem`, namespace
`Langlands.Geometry.Building.AffineRootSystem`.

This module formalizes the generic affine-root-system vocabulary of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), §1.3 (book PDF pp. 45–61; printed
pp. 14–30). It covers the axioms AR 1–AR 4, reduced systems, affine root hyperplanes,
the affine reflections and the affine Weyl group, `Ψ_x`, special and extra special
points (Definition 1.3.39), and the facets, facet closures, faces, chambers, vertices and
positive roots of the hyperplane arrangement. It follows the *Corrections and additions*
of 1 November 2024 where they touch these items: AR 4 includes an infiniteness condition,
and the facet notion and closure formula are the ones the corrections recall for
Proposition 1.3.35 (corrections PDF pp. 2–4).

Everything is stated for an arbitrary set `Ψ` of affine functionals on an affine
space, so the module involves no field, reductive group, root group, valuation,
apartment or building. A later module is meant to apply these definitions to the
affine roots of actual Kaletha–Prasad valuation data on an actual apartment. That
application, the choice of apartment (reduced or enlarged) and the comparison with the
normalizer action are not part of this module.

## Setting

- `V` is a real vector space (`[AddCommGroup V] [Module ℝ V]`) and `A` is an affine
  space under it (`[AddTorsor V A]`). No origin of `A` is chosen, and `A` is kept
  distinct from `V`.
- KP's `A*` (affine functionals on `A`) is Mathlib's `A →ᵃ[ℝ] ℝ`, a real vector space.
  A set of affine roots is `Ψ : Set (A →ᵃ[ℝ] ℝ)`.
- KP's derivative `∇ψ = ψ̇ ∈ V*` is `ψ.linear : V →ₗ[ℝ] ℝ`, which is
  `Module.Dual ℝ V`.
- KP assumes `V` finite-dimensional. The definitions do not need this, and the
  module does not assume it. For a set satisfying `IsAffineRootSystem`, AR 1 already
  forces it: `V*` is spanned by the finite set `∇Ψ`. This is a remark and is not
  proved in Lean.

## Derivatives and hyperplanes

- `derivativeRoots Ψ` is `Φ = ∇Ψ = {ψ̇ | ψ ∈ Ψ} ⊆ V*` (KP Definition 1.3.1, AR 1;
  Proposition 1.3.3 calls it the derivative root system). Laws:
  `mem_derivativeRoots`, `linear_mem_derivativeRoots` and `derivativeRoots_mono`.
- `hyperplane ψ : AffineSubspace ℝ A` is `H_ψ = {x ∈ A | ψ(x) = 0}` (KP
  Definition 1.3.7), and `mem_hyperplane` unfolds it. For a constant nonzero `ψ`
  it is empty (`⊥`). AR 1 excludes constants.
- `exists_apply_eq_zero`: a functional with `ψ̇ ≠ 0` vanishes somewhere.
  `hyperplane_ne_bot`: its hyperplane is nonempty.
- `direction_hyperplane`: for `ψ̇ ≠ 0`, the direction of `H_ψ` is `ker ψ̇`. This is
  the root hyperplane `∇H_ψ = H_ψ̇` of KP Definition 1.3.7.
- "Parallel" is Mathlib's `AffineSubspace.Parallel` (notation `∥`): `s₂` is a translate
  `s₁ + v` of `s₁`. `hyperplane_parallel_iff`: for `ψ̇ ≠ 0 ≠ ψ̇'`,
  `H_ψ ∥ H_ψ' ↔ ker ψ̇ = ker ψ̇'`.
- `hyperplane_comp`: `H_(ψ ∘ e)` is the preimage of `H_ψ` under an affine automorphism
  `e`. `parallel_map_affineEquiv` and `parallel_comap_affineEquiv`: images and
  preimages under an affine automorphism preserve parallelism. (Mathlib has no such
  lemma for `AffineSubspace.Parallel`, so these are proved here.)

## Reduced systems

- `IsReduced Ψ`: `ψ ∈ Ψ → 2ψ ∉ Ψ` (KP Definition 1.3.4).
- `nonDivisibleRoots Ψ` is `Ψ_nd = {ψ ∈ Ψ | ψ/2 ∉ Ψ}`, and `nonMultipliableRoots Ψ`
  is `Ψ_nm = {ψ ∈ Ψ | 2ψ ∉ Ψ}` (KP Remark 1.3.5). Here `ψ/2` is `(2 : ℝ)⁻¹ • ψ`.
- `nonDivisibleRoots_subset` and `nonMultipliableRoots_subset` give the inclusions in `Ψ`.
  `nonDivisibleRoots_eq_self_iff` and `nonMultipliableRoots_eq_self_iff` say
  `Ψ_nd = Ψ ↔ Ψ` is reduced and `Ψ_nm = Ψ ↔ Ψ` is reduced. Together these give the
  statement of Remark 1.3.5 that `Ψ_nd = Ψ = Ψ_nm` exactly when `Ψ` is reduced. KP's
  other claims in Remark 1.3.5 are not formalized: that `Ψ_nd` and `Ψ_nm` are
  affine root systems with the same hyperplanes and Weyl group, and the inclusions
  of derivative systems.

## Affine reflections and the affine Weyl group

- `IsCoroot Ψ ψ v` says that `ψ̇(v) = 2` and `η - η̇(v) ψ ∈ Ψ` for every `η ∈ Ψ`. This
  is the condition of AR 2 on the vector `ψ̇∨ := v ∈ V`: the reflection
  `r_(ψ,v)(η) = η - η̇(v) ψ` of `A*` preserves `Ψ`.
- `affineReflection ψ hv : A ≃ᵃ[ℝ] A`, for `hv : ψ̇(v) = 2`, is the dual reflection
  `x ↦ x - ψ(x) v` of KP Remark 1.3.2(3). In Lean it is written `(-ψ x) • v +ᵥ x`.
  Laws:
  - `affineReflection_apply`.
  - `affineReflection_linear`: the derivative is Mathlib's `Module.reflection hv`,
    `w ↦ w - ψ̇(w) v`.
  - `apply_affineReflection`: `ψ(r x) = -ψ(x)`.
  - `affineReflection_apply_of_mem`: `r` fixes `H_ψ` pointwise.
  - `affineReflection_involutive` and `affineReflection_mul_self`: `r² = 1`.
  - `comp_affineReflection`: `η ∘ r = η - η̇(v) ψ`. So pulling back along the
    reflection of `A` is exactly KP's reflection `r_(ψ,v)` of `A*` from AR 2.
- `rootStabilizer Ψ : Subgroup (A ≃ᵃ[ℝ] A)` is the group of affine automorphisms `e`
  with `η ∘ e ∈ Ψ ↔ η ∈ Ψ` for every affine functional `η`, so pull-back by `e`
  permutes `Ψ`. This is a derived auxiliary group with no KP number. It provides
  one hypothesis under which both the affine Weyl group and, later, a normalizer
  action can be shown to preserve special points.
- `affineWeylGroup Ψ` is the subgroup of `A ≃ᵃ[ℝ] A` generated by all
  `affineReflection ψ hv.1` with `ψ ∈ Ψ` and `hv : IsCoroot Ψ ψ v`. This is KP's
  `W(Ψ)` of Definition 1.3.1, the group generated by the `r_(ψ, ψ̇∨)`, realized through
  its action on `A` (Remark 1.3.2(3)) rather than on `A*`. The two realizations
  correspond by `comp_affineReflection`. Laws:
  - `affineReflection_mem_affineWeylGroup`.
  - `affineReflection_mem_rootStabilizer`.
  - `affineWeylGroup_le_rootStabilizer`: every element of `W(Ψ)` permutes `Ψ` by
    pull-back.

  Derived point: the generating set uses every vector `v` with `IsCoroot Ψ ψ v`.
  For an affine root system KP Remark 1.3.2(2) (via Bourbaki, *Lie Groups and Lie
  Algebras* VI §1 no. 1, Lemma 1) shows that this vector is unique, so the generators
  are exactly KP's `r_ψ`. The [AffineWeylGroups](AffineWeylGroups.md) module
  proves this uniqueness in Lean. For an arbitrary `Ψ` the group may be larger
  than the group generated by any one choice of coroots.

## The axioms (`IsAffineRootSystem`)

`IsAffineRootSystem Ψ` is a `Prop`-valued structure with these fields (KP
Definition 1.3.1):

- AR 1: `span_eq_top` (`Ψ` spans `A*`), `linear_ne_zero` (no element of `Ψ` is
  constant) and `finite_derivativeRoots` (`Φ = ∇Ψ` is finite).
- AR 2: `exists_isCoroot`, every `ψ ∈ Ψ` has some `v` with `IsCoroot Ψ ψ v`.
- AR 3: `coroot_integral`, for `ψ, η ∈ Ψ` and every `v` with `IsCoroot Ψ η v`,
  `ψ̇(v) ∈ ℤ`. KP states AR 3 for the unique `η̇∨`. Quantifying over every
  AR 2 vector says the same thing once uniqueness is known, and makes sense without it.
- AR 4, as corrected (corrections PDF p. 2: "Axiom AR 4 should include the requirement
  that the set `{ψ ∈ Ψ | ψ̇ = a}` is infinite"):
  - `infinite_fiber`: for each `ψ ∈ Ψ`, `{η ∈ Ψ | η̇ = ψ̇}` is infinite. Every
    `a ∈ Φ` is some `ψ̇`, so this is the corrections' requirement verbatim.
  - `finite_bounded`: for each `ψ ∈ Ψ` and `M : ℝ` the set
    `{η ∈ Ψ | η̇ = ψ̇ ∧ ∀ x, |η(x) - ψ(x)| ≤ M}` is finite. This is a derived
    reformulation of "for each `a ∈ Φ`, `{ψ ∈ Ψ | ψ̇ = a}` has no accumulation point". If `η̇ = ψ̇` then
  `η - ψ` is a constant `c`, so the fibre over `a = ψ̇` is `ψ + C` for a set `C ⊆ ℝ`.
  This fibre lies on the closed line `ψ + ℝ` of the finite-dimensional space `A*`.
  Such a set has no accumulation point exactly when `C` meets every bounded interval
  in a finite set. The equivalence is a remark and is not proved in Lean.

`IsAffineRootSystem.neg_mem`: an affine root system is stable under `ψ ↦ -ψ`. This is
AR 2 applied with `η = ψ`, because `ψ - 2ψ = -ψ`.

None of KP's propositions about affine root systems are formalized here: 1.3.3,
1.3.11, 1.3.12, Lemma 1.3.6, local finiteness (Lemma 1.3.10), 1.3.35(1),(2),(4)–(8),
Lemma 1.3.42 and Proposition 1.3.43. In particular, the existence of special or extra
special points, "extra special ⇒ special" and "special ⇒ vertex" are not proved.

## `Ψ_x`, special and extra special points

- `vanishingRoots Ψ x` is `Ψ_x = {ψ ∈ Ψ | ψ(x) = 0}` (KP Proposition 1.3.35). Laws:
  `mem_vanishingRoots`, `vanishingRoots_subset` and
  `mem_vanishingRoots_iff_mem_hyperplane`.
- `IsSpecialPoint Ψ x` is KP Definition 1.3.39(1), verbatim: for each `ψ ∈ Ψ` there is
  `ψ' ∈ Ψ_x` with `H_ψ ∥ H_ψ'`. The predicate refers to the hyperplanes of `Ψ` only,
  not to any subgroup.
  - `isSpecialPoint_iff_ker`: if no element of `Ψ` is constant, this is equivalent to
    "for each `ψ ∈ Ψ` some `ψ' ∈ Ψ_x` has `ker ψ̇ = ker ψ̇'`".
- `IsRootBasis Φ B`, for `Φ, B ⊆ V*`, is a `Prop`-valued structure: `B ⊆ Φ`; `B` is
  linearly independent and spans `V*`; and every `a ∈ Φ` is `Σ_b c_b b` for a finitely
  supported `c : B →₀ ℤ` whose coefficients are all `≥ 0` or all `≤ 0`. This is the
  notion of a basis (base) of a finite root system, as in Bourbaki, *Lie Groups and Lie
  Algebras* VI §1 no. 5, Theorem 2 and Definition 2; no. 6, Theorem 3; and
  no. 7, Proposition 20, Corollary 3. KP uses bases throughout §1.3 (e.g.
  Proposition 1.3.35(6), Proposition 1.3.43). The ambient-space basis condition
  is stated for `V*` because KP's `Φ` lies in `V*`.
- `IsExtraSpecialPoint Ψ x` is KP Definition 1.3.39(2): some `Ψ₀ ⊆ Ψ_x` has
  `IsRootBasis (∇Ψ) (∇Ψ₀)`. KP writes "there exist `ψ_1, …, ψ_ℓ ∈ Ψ_x` such that
  `{ψ̇_1, …, ψ̇_ℓ}` is a basis of `Φ`". Choosing a subset rather than a list is
  equivalent, because a basis of `Φ` is finite. KP Remark 1.3.40 records that
  Macdonald calls these points "special". The module follows KP, Bourbaki,
  Bruhat–Tits and Tits in calling the Definition 1.3.39(1) points special.

## Facets, closures, faces, chambers, vertices and positive roots

KP Remark 1.3.16 describes chambers as the connected components of
`A - ⋃ H_ψ`, and the other facets by iterating within the strata. The 2024
corrections to Proposition 1.3.35 (corrections PDF p. 4) make the notion precise. They
recall from Bourbaki, *Lie Groups and Lie Algebras* V §1 no. 2, the facets of a locally
finite set of hyperplanes: the classes of the relation "for every hyperplane, the two
points either both lie on it or lie on the same side of it". They add: "The facets in
`A` that we have been discussing so far are those for the set `H` of all affine root
hyperplanes." The module uses exactly this relation:

- `facetRel Ψ x y`: `sign ψ(x) = sign ψ(y)` for every `ψ ∈ Ψ`, with Mathlib's
  `SignType.sign`. So for every root hyperplane, `x` and `y` either both lie on it or
  lie strictly on the same side. `facetRel_equivalence` proves it is an equivalence
  relation, and `facetSetoid Ψ` is the corresponding setoid.
- `facet Ψ x` is the class of `x`, and `IsFacet Ψ F` says that `F` is such a class.
- `IsChamber Ψ C` says `C` is the facet of a point that lies on no `H_ψ`. Such a
  facet is `{y | sign ψ(y) = sign ψ(x) for all ψ}`, an intersection of open half-spaces.
- `IsVertex Ψ x` says `facet Ψ x = {x}`. KP calls the facets of smallest dimension
  vertices. For an affine root system these are the facets of dimension `0`, which are
  single points (KP Proposition 1.3.22(6) gives the vertices of a chamber as points).
  So the module defines a vertex as a point whose facet is that point alone. This is
  a derived formulation.
- `facetClosure Ψ x` is the set of `y` such that, for every `ψ ∈ Ψ`, `sign ψ(y)` is
  `0` or `sign ψ(x)`. This is the corrections' closure formula
  `F̄ = ⋂_{x ∈ H} H ∩ ⋂_{x ∉ H} D̄_H(x)`. Here `D̄_H(x) = D_H(x) ∪ H` is the closed side of
  `H` containing `x`, and `H` runs over the hyperplanes `H_ψ`, `ψ ∈ Ψ`. If
  `ψ(x) = 0`, the condition says `ψ(y) = 0`. Otherwise it says that `ψ(y)` is `0` or has
  the sign of `ψ(x)`. Non-constant functionals with the same hyperplane are nonzero
  multiples of each other, so they impose the same condition. A nonzero constant
  imposes no condition, matching its empty zero set.
- `IsFaceOf Ψ F' F`: `F'` is a facet contained in `facetClosure Ψ x` for a point `x`
  with `facet Ψ x = F`. This is KP Remark 1.3.16: "A face of a facet `F` is a facet
  `F'` contained in the closure `F̄` of `F`".
- `positiveRoots Ψ C` and `negativeRoots Ψ C` are `Ψ(C)^+ = {ψ ∈ Ψ | ψ > 0 on C}` and
  `Ψ(C)^- = {ψ ∈ Ψ | ψ < 0 on C}` (KP Definition 1.3.18). The definitions apply to any
  set `C`; KP uses them for chambers. KP's `Ψ_F(C)^+ = Ψ_F ∩ Ψ(C)^+` of Proposition
  1.3.35(7) is `vanishingRoots Ψ x ∩ positiveRoots Ψ C` for `x ∈ F`, and
  `Ψ(C)^nd,+` is `positiveRoots Ψ C ∩ nonDivisibleRoots Ψ`.

The facet relation and the closure formula are defined for every `Ψ`, without a
topology on `A`. Bourbaki's results that facets partition `A` into the strata of
Remark 1.3.16, that the classes off all hyperplanes are the connected components of
`A - ⋃ H_ψ`, and that `facetClosure` is the topological closure of the facet all
assume a locally finite hyperplane family. KP Lemma 1.3.10 gives local finiteness for
affine root systems. None of these facts is proved in Lean. Walls and the simple affine
roots `Ψ(C)_0` (Definition 1.3.19) are not defined here, because "wall" refers to the
codimension of a face.

Laws:

- `mem_facet`, `mem_facet_self`, `facet_eq_facet_iff` (`facet x = facet y ↔ facetRel x y`),
  `facet_eq_of_mem`, `isFacet_facet` and `IsChamber.isFacet`.
- `vanishingRoots_eq_of_facetRel`: `Ψ_x` depends only on the facet of `x` (KP
  Proposition 1.3.35(3)).
- `facet_subset_facetClosure` and `mem_facetClosure_self`: a facet lies in its closure.
  `facetClosure_eq_of_facetRel`: the closure depends only on the facet.
- `facet_subset_facetClosure_iff`: a facet lies in `facetClosure Ψ x` as soon as one
  of its points does. `mem_facetClosure_trans`: the relation `y ∈ facetClosure Ψ x`
  (KP Notation 1.3.34, `F_y ≺ F_x`) is transitive.
- `IsChamber.mem_positiveRoots_or_mem_negativeRoots`: on a chamber every root is
  positive or negative (KP, after Definition 1.3.18).
- `facet_subset_hyperplane`: the facet of `x` lies in `H_ψ` for each `ψ ∈ Ψ_x`.
- `isSpecialPoint_congr` and `isExtraSpecialPoint_congr`: both notions depend only on
  the facet.

## Transport by root-preserving automorphisms

For `e ∈ rootStabilizer Ψ` (in particular for `e ∈ affineWeylGroup Ψ`):

- `comp_mem_iff`: `η ∘ e ∈ Ψ ↔ η ∈ Ψ`. `comp_inv_comp` is the identity
  `(η ∘ e⁻¹) ∘ e = η`, which holds for any affine automorphism.
- `mem_vanishingRoots_apply`: `η ∈ Ψ_(e x) ↔ η ∘ e ∈ Ψ_x`.
- `facetRel_apply_iff`: `e` preserves the facet relation.
- `IsSpecialPoint.of_apply` and `isSpecialPoint_apply_iff`:
  `x` is special if and only if `e x` is special.

KP uses the invariance of these notions under `W(Ψ)`, for example in the proof of
Proposition 1.3.43(5). Invariance of extra special points is not formalized.

## Scope and provenance

- Source: Kaletha–Prasad (2023), registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The relevant
  items are Definition 1.3.1, Remark 1.3.2, Definitions 1.3.4 and 1.3.7, Remarks 1.3.5
  and 1.3.16, Proposition 1.3.35, Definition 1.3.39 and Remark 1.3.40, on book PDF
  pp. 45–61. Also used are the *Corrections and additions* of 1 November 2024
  (`kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`), PDF p. 2
  (AR 4) and PDF p. 4 (facets and facet closures for Proposition 1.3.35). The other
  §1.3 corrections concern proofs and statements not formalized here.
- Derived or auxiliary items, explained above: the AR 4 reformulation, AR 3 for every
  AR 2 vector, `rootStabilizer`, generating `W(Ψ)` from all AR 2 vectors, Bourbaki's
  sign relation for facets (as in the corrections), the sign form of the corrections'
  closure formula, chambers as facets off every hyperplane, vertices as singleton
  facets, and `IsRootBasis` (Bourbaki's basis of a root system).
- The module does not identify any `Ψ` coming from a reductive group. Choosing the
  apartment (KP 6.1.27 uses the adjoint torus `S_ad`), the affine roots of actual
  valuation data (KP 6.3–6.4) and the normalizer action belong to later modules.
  The same holds for parahoric subgroups, `G(F)^0`, `G(F)^1` and `K_x`.
