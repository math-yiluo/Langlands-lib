# Algebras graded by a commutative group with pieces of rank at most one

This module is pure algebra, with no representation theory. It isolates the
algebraic part of the proofs of Renard VI.4.4 (the Theorem, the Corollary and the
Proposition on the center of `A = End(ind ρ)`). It records the abstract
structure Renard uses in VI.4.3: `A` is graded by the group `⁰G\N`, each graded
piece has dimension at most one, and nonzero homogeneous elements are
invertible. The module then proves the consequences of this structure that the
three VI.4.4 results need. All declarations are in namespace
`Langlands.RankOneGraded`.

## Setting and the definition

Let `ι` be an additive commutative group with decidable equality, `k` a field and
`R` a `k`-algebra. Let `𝒜 : ι → Submodule k R` be a grading of `R` in the sense of
Mathlib's `GradedAlgebra 𝒜`: `R` is the internal direct sum of the `𝒜 i`, with
`1 ∈ 𝒜 0` and `𝒜 i * 𝒜 j ≤ 𝒜 (i + j)`. The grading index is written additively so
that Mathlib's `GradedAlgebra` API applies. In the VI.4.4 application, `ι` is
`Additive (G(F) ⧸ ⁰G)`.

**Definition.** `IsRankOneGrading 𝒜` is the proposition with two fields:

- `rank_le_one : ∀ i, Module.rank k (𝒜 i) ≤ 1`: every homogeneous piece has rank
  at most one;
- `isUnit_of_mem : ∀ i x, x ∈ 𝒜 i → x ≠ 0 → IsUnit x`: every nonzero
  homogeneous element is a unit of `R`.

### Provenance

This is a derived definition. It is not stated as such in the source. It is an
abstraction of the structure of `A = H(N, ρ)` that Renard establishes in
VI.4.3 "Structure de A" (printed pp.154–155 / PDF pp.160–161). There, each
space `F_x(ρ)` of functions supported in `⁰G x` has dimension at most one, by the
identification with `Hom_{⁰G}(ρ^x, ρ)` and Schur's lemma. Supports multiply
(VI.4.3.1). Nonzero homogeneous elements are invertible, and `A` is a twisted
Laurent polynomial algebra (VI.4.3.2–VI.4.3.3). The results proved here are
the algebraic content of the proof of the Theorem of VI.4.4 and of the
Corollary and Proposition that follow it (printed pp.158–159 / PDF pp.164–165). The route
below is not Renard's. Renard identifies the center through the subgroups
`T ⊂ H ⊂ N` and the Lemma of VI.4.4. Here the center and the rank are
computed from the commutation scalars of the twisted group algebra and from one
finite-dimensional simple module. The identification of the radical below with
`T/⁰G` is not part of this module.

## Basic facts (namespace `IsRankOneGrading`, for `h𝒜 : IsRankOneGrading 𝒜`)

These lemmas need no hypothesis beyond the grading itself:
`eq_zero_of_decompose`, `mem_of_decompose_eq_zero`, `mem_center_of_commute` (an
element commuting with every homogeneous element lies in
`Subalgebra.center k R`), and `decompose_mem_center` (homogeneous components of
a central element are central).

Under `h𝒜`:

- `exists_smul_eq`: in a piece, every element is a scalar multiple of any given
  nonzero element;
- `mul_ne_zero`: a product of a nonzero homogeneous element and a nonzero element
  is nonzero;
- `exists_inv_mem`: a nonzero element of `𝒜 i` has a two-sided inverse in
  `𝒜 (-i)`, using the Mathlib lemmas `coe_decompose_mul_add_of_left_mem` and
  `decompose_of_mem_ne`;
- `exists_algebraMap_eq_of_mem_zero`: for nontrivial `R`, `𝒜 0` consists of
  scalars.

## Support, radical and the center

From here on `R` is nontrivial.

- `support : AddSubgroup ι` is the set of degrees `i` with `𝒜 i ≠ ⊥`.
  `mem_support_iff` says `i ∈ support` iff `𝒜 i` has a nonzero element.
- `radical : AddSubgroup ι` is the set of degrees `i` with `𝒜 i ≠ ⊥` and
  `𝒜 i ⊆ Subalgebra.center k R`. It is contained in the support
  (`radical_le_support`). In twisted-group-algebra terms, it is the radical of
  the commutator bicharacter on the support.
- `mem_radical_of_mem_center`: a nonzero central element of degree `i` puts `i`
  in the radical.
- `mem_center_iff`: an element `x` is central if and only if every homogeneous
  component `decompose 𝒜 x i` with `i ∉ radical` is zero. This is the abstract
  form of the Theorem of VI.4.4: the center is the part of `R` supported on the
  radical.
- `exists_mul_eq_smul_mul`: if `w ∈ 𝒜 i` is nonzero and `i ∉ radical`, there is a
  nonzero homogeneous `v` and a scalar `c ≠ 1` with `w * v = c • (v * w)`.

## Freeness over the center

- `Cosets` is the quotient `support ⧸ radical` (as `h𝒜.radical.addSubgroupOf
  h𝒜.support`).
- `rep q` is the degree of a chosen representative of `q`. `mono q` is a chosen
  nonzero element of `𝒜 (rep q)`, and `monoInv q ∈ 𝒜 (-rep q)` is its two-sided
  inverse.
- `linearIndependent_mono` and `span_mono`: the family `mono` is linearly
  independent over `Subalgebra.center k R` and spans `R`, where the center acts
  by left multiplication (`smul_def`). Independence uses `mem_center_iff`: the
  degree-`(a + rep p)` component of a relation `∑ g_q * mono q = 0` with `a` in
  the radical reduces to `g_p`'s degree-`a` component times `mono p`. Spanning
  writes a homogeneous `m` of degree `i` as `(m * monoInv q) * mono q`, where
  `q` is the class of `i` and `m * monoInv q` has degree in the radical.
- `basis : Module.Basis h𝒜.Cosets (Subalgebra.center k R) R` is the resulting
  basis, with `basis_apply : basis q = mono q`.

## Actions on a vector space and the count

Section `Represent` has no grading hypothesis. `ρ : R →ₗ[k] Module.End k M` is
a `k`-linear map, and `IsMulOrAntiMul ρ` says that `ρ` is multiplicative or
anti-multiplicative. The anti-multiplicative case covers right modules: for
`End I`, whose product is `α * β = β ≫ α`, the action on `Hom(I, π)` by
precomposition is anti-multiplicative. The section proves trace identities
(`trace_mul_eq`, `trace_mul_comm`), and `exists_eq_algebraMap_of_mem_center`:
if `ρ` is surjective, central elements act by scalars (Mathlib's
`Algebra.IsCentral` for `Module.End k M`). It also proves two general facts:

- `exists_forall_eq_smul_of_isSimpleModule` (**Burnside's theorem**): if `V` is a
  simple module over a `k`-algebra `A`, finite-dimensional over an algebraically
  closed `k`, then every `k`-linear endomorphism of `V` is the action of some
  `a : A`. The proof combines Mathlib's Schur lemma over algebraically closed
  fields (`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`) with the
  Jacobson density theorem (`jacobson_density`) applied to a finite basis.
- `isNoetherianRing_of_algEquiv_monoidAlgebra`: a commutative `k`-algebra
  isomorphic to `MonoidAlgebra k Γ` for a finitely generated commutative group
  `Γ` is noetherian (Mathlib's `Algebra.FiniteType.isNoetherianRing`).

Section `Count` (under `h𝒜`):

- `trace_eq_zero_of_not_mem_radical`: a homogeneous element of degree outside
  the radical acts with trace zero. With `w * v = c • (v * w)`, `c ≠ 1` and `v`
  invertible, the trace of `ρ w` equals `c` times itself.
- `linearIndependent_map_mono`: if `k` has characteristic zero, `M` is
  finite-dimensional and nonzero, and `ρ 1 = 1`, then the operators
  `ρ (mono q)` are `k`-linearly independent. Pairing a relation with
  `ρ (monoInv p)` under the trace isolates the coefficient of `p`.
- `map_mem_span_map_mono`: if `ρ` is surjective, every `ρ x` lies in the
  `k`-span of the `ρ (mono q)`.
- `finite_cosets_and_card_eq`: under these hypotheses (characteristic zero,
  `M` finite-dimensional and nonzero, `ρ 1 = 1`, `IsMulOrAntiMul ρ`, `ρ`
  surjective), `Cosets` is finite and `Nat.card Cosets = (finrank k M)^2`. The
  operators `ρ (mono q)` form a `k`-basis of `Module.End k M`. In VI.4.4,
  `M = Hom(I, π)` has dimension `m`, and Burnside's theorem gives surjectivity,
  so `R` has rank `m^2` over its center.

## The center as a group algebra

Section `Center`, for `ρ` as above with `M` nontrivial:

- `exists_mem_map_eq_one`: if `ρ 1 = 1` and `ρ` is surjective, every degree `a` in
  the radical carries an element `x ∈ 𝒜 a` with `ρ x = 1`;
- `eq_of_map_eq_one`: in each degree at most one element acts as the identity;
- `exists_algEquiv_center`: under the same hypotheses there is a `k`-algebra
  isomorphism `e : MonoidAlgebra k (Multiplicative radical) ≃ₐ[k]
  Subalgebra.center k R` such that for every `a`, `e (of a)` lies in
  `𝒜 a` and acts as the identity on `M`. The normalised elements form a group
  homomorphism `Multiplicative radical →* center`, by uniqueness of the
  normalised element in each degree. Its `MonoidAlgebra.lift` is injective
  because distinct degrees are independent, and surjective by
  `mem_center_iff`. No character of the radical has to be chosen. In VI.4.4 this
  normalisation makes the element attached to `t` act as the identity on
  `Hom(I, π)`, which is the `ω = 1` case of the Proposition.

## Noetherianity

`isNoetherianRing_of_finite`: if `Cosets` is finite and the center is a
noetherian ring, then `R` and `Rᵐᵒᵖ` are noetherian rings. `R` is a finite module
over the noetherian center, via `basis`. Left ideals are center-submodules, so
`R` is noetherian. For `Rᵐᵒᵖ` the center acts on `Rᵐᵒᵖ` through `op`, which is
a center-linear equivalence `R ≃ Rᵐᵒᵖ`, and right ideals of `R` are again
center-submodules (`isNoetherian_of_tower`). This gives the Corollary of VI.4.4
once the center is identified with the group algebra of a finitely generated
group.
