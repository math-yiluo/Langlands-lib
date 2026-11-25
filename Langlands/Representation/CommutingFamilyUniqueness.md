# Uniqueness for commuting families of isotypic local actions

`Langlands/Representation/CommutingFamilyUniqueness.lean` proves an abstract,
purely algebraic uniqueness theorem for spaces carrying a family of pairwise
commuting monoid actions. It is the algebraic core of the implication "same
local components ⇒ equivalent" in
`Langlands.Automorphic.LocalComponentDeterminationStatement`: two irreducible
representations of a restricted product that are isotypic of the same
irreducible type at every factor are isomorphic.

Everything is over an arbitrary field `k`. No topology, smoothness or
admissibility enters; these are replaced by explicit hypotheses (scalar
self-intertwiners, almost-everywhere fixed lines, almost-everywhere fixed
vectors).

## Main theorem

`Langlands.CommutingFamily.exists_linearEquiv_of_isotypic`. Data:

- an index type `ι`, monoids `G i`, and two families of representations
  `σ i : Representation k (G i) V`, `σ' i : Representation k (G i) V'`, each
  pairwise commuting (`RestrictedTensor.CyclicEvaluation.Commuting`, hypotheses
  `hσ`, `hσ'`);
- `IsJointlyIrreducible σ` and `IsJointlyIrreducible σ'`: the space is
  nontrivial and every subspace stable under all `σ i g` is `⊥` or `⊤`;
- irreducible representations `τ i` of `G i` on `W i` whose self-intertwiners
  are scalars (`hS`);
- isotypy (`hiso`, `hiso'`): for every `i`, the ranges of the intertwining
  maps `τ i → σ i` span `V`, and likewise for `σ'`;
- sets `H i ⊆ G i` such that, for all but finitely many `i`, the vectors of
  `W i` fixed by `H i` are multiples of one vector `w₀` (`hsph`);
- smoothness (`hsm`, `hsm'`): every vector of `V` (of `V'`) is fixed by `H i`
  for all but finitely many `i`.

Conclusion: there is a linear equivalence `Φ : V ≃ₗ[k] V'` with
`Φ (σ i g v) = σ' i g (Φ v)` for all `i`, `g`, `v`.

`hsph` asks only that the fixed vectors lie on a line; it does not require a
nonzero fixed vector. In the application `H i` is the maximal compact
subgroup `GL_n(𝒪_v)` and `hsph` is the uniqueness of the spherical line.

## Auxiliary results

**Density** (`exists_asAlgebraHom_eq_on`): an irreducible monoid
representation with scalar self-intertwiners satisfies Jacobson density: every
linear endomorphism agrees with some monoid algebra element on a given finite
set. This is Mathlib's `jacobson_density` applied to `τ.asModule`; the
Library's `FiniteTensor.exists_asAlgebraHom_eq_on` is the same statement for
groups.

**Finite tensor products** (`map_slot_asAlgebraHom_mem`,
`eq_top_of_slot_stable`): in a finite tensor product of such representations,
a nonzero subspace stable under every one-slot action is everything (monoid
version of the main step of the Library's `FiniteTensor.isIrreducible_external`).
Proof: expand a nonzero vector in the product basis, use density in every slot
to project onto one basis tensor and then to any pure tensor.

**Cyclic evaluation** (`factorRep`, `evalStage_injective`, `eval_injective`):
for a nonzero `v` whose cyclic factors `Factor σ v i` (the `σ i`-span of `v`)
are irreducible with scalar self-intertwiners, the Library's cyclic evaluation
maps `evalStage σ hσ v S` (finite stages) and `eval σ hσ v E` (restricted
tensor product of the cyclic factors) are injective: the kernel is stable
under the slot actions (`evalStage_coordinateAction`) and does not contain the
pure tensor of generators.

**One index** (section `Local`), for `τ` irreducible with scalar
self-intertwiners and `σ` that is `τ`-isotypic:

- `evalHom τ σ : τ.IntertwiningMap σ ⊗ W → V`, `f ⊗ w ↦ f w`, intertwines the
  action on `W` (`evalHom_lTensor`) and is bijective (`evalHom_injective`,
  `evalHom_surjective`). Injectivity uses `exists_lTensor_eq_tmul`: density
  moves a nonzero tensor to a nonzero pure tensor `m ⊗ w`.
- `IsImage τ σ w x` means `x = f w` for an intertwining map `f`.
  `exists_isImage`: every nonzero `x` is moved by the monoid algebra to a
  nonzero image of any prescribed nonzero `w₁`. `isImage_of_fixed`: if the
  `H`-fixed vectors of `τ` are multiples of `w₀`, every `H`-fixed vector of `σ`
  is an image of `w₀` (via the Library's
  `FiniteTensor.lTensor_eq_of_forall_fixed`).
- `nonempty_equiv_orbitSpan`: a nonzero image of `w` generates a cyclic
  subrepresentation equivalent to `τ`; `isIrreducible_of_equiv`,
  `scalar_of_equiv` transport irreducibility and scalar self-intertwiners.
- `IsImage.annihilator_le`: if `x ≠ 0` and `y` are images of the same `u`,
  every monoid algebra element killing `x` kills `y`.

**The family** (section `Global`):

- `span_algebraProduct_eq_top`: in a jointly irreducible space the vectors
  `algebraProduct σ hσ S a x` (finite products of monoid algebra elements at
  distinct indices applied to a nonzero `x`) span everything; uses
  `single_mul_algebraProduct`.
- `exists_isImage_everywhere` (selection): from a nonzero vector that is an
  image at all indices outside a finite set `E`, induction on `E` with
  `exists_isImage` and commutation produces a nonzero vector that is an image
  at every index (with a side condition `P i w` on the vector of `τ i`).
- `transfer`, `transfer_presentation`, `transfer_generator`: the map of cyclic
  factors `σ i(a) x ↦ σ' i(a) y`, well defined when every relation of `x` is a
  relation of `y`.
- `exists_map_algebraProduct`: under the same hypothesis there is a linear
  map `Φ` with `Φ (algebraProduct σ hσ S a x) = algebraProduct σ' hσ' S a y`;
  it is `eval' ∘ mapWithBound (transfer) ∘ eval⁻¹`, where `eval` is bijective
  by `eval_injective` and `span_algebraProduct_eq_top`.

## The implemented proof of the main theorem

1. Pick `x₀ ≠ 0` in `V` and a finite set `E` outside which the fixed line of
   `τ i` exists and `x₀` is `H i`-fixed. Outside `E`, `x₀` is an image of the
   fixed vector `w₀` (`isImage_of_fixed`). Selection gives `x ≠ 0` that is an
   image `x = f_i (w i)` at every `i`, with `w i ≠ 0`.
2. Pick `y₀ ≠ 0` in `V'` and a finite set `E'` outside which the fixed line
   exists and both `x` and `y₀` are `H i`-fixed. Outside `E'`, `x` and `y₀`
   are images of the same `w₀`. Selection in `V'` with side condition
   "`x` is an image of the same vector" gives `y ≠ 0` such that at every `i`
   some `u` has both `x` and `y` as images.
3. Hence every relation of `x` at `i` is one of `y`
   (`IsImage.annihilator_le`), and every cyclic factor of `x` is equivalent to
   `τ i`, so irreducible with scalar self-intertwiners.
4. `exists_map_algebraProduct` gives `Φ`. It commutes with every `σ i g`
   because `σ i g · algebraProduct S a` is again an `algebraProduct`
   (`apply_algebraProduct`) and these vectors span `V`. `Φ x = y ≠ 0`, so by
   joint irreducibility of `σ` the kernel (stable) is `⊥`; by joint
   irreducibility of `σ'` the range (stable, nonzero) is `⊤`.

The equivalence is `LinearEquiv.ofBijective Φ`.

## Provenance

This is a derived, abstract form of the uniqueness of factorizations in D.
Flath, *Decomposition of representations into tensor products*, Proceedings
of Symposia in Pure Mathematics 33, part 1 (1979), printed pp.179–183
(source `flath-1979-tensor-products`, file
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`,
SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`,
one-based PDF pp.175–179):

- end of the proof of Theorem 1, printed p.180 (PDF p.176): "The class of
  `W_i` is determined by that of `W`, for the restriction of `W` to `G_i` is
  `W_i`-isotypic";
- printed p.181 (PDF p.177): independence of the restricted tensor product
  from the choice of the vectors `x_v` on the spherical lines, and Theorem 3,
  "Every admissible irreducible representation of `G(𝔸)` is factorizable.
  The factors are unique up to equivalence."

It is also the uniqueness part of Getz–Hahn, *An Introduction to Automorphic
Representations* (source `getz-hahn-2024-automorphic-representations`,
SHA256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`),
Theorem 6.3.7 and its proof, printed pp.165–166 (PDF pp.179–180).

The sources use factorization of admissible representations to compare the
two restricted tensor products. The Lean theorem takes scalar
self-intertwiners, fixed-line bounds and eventual fixed vectors as explicit
hypotheses. Its internal selection argument produces one vector on each
side with matching local relations. It uses restricted tensor products of
the resulting cyclic spaces and the Library's cyclic evaluation maps
(`Langlands/Representation/RestrictedTensor/CyclicEvaluation.lean`) to
prove the intertwining equivalence.

## Checks

A check of `Langlands.Representation.CommutingFamilyUniqueness`: no errors,
no warnings; `exists_linearEquiv_of_isotypic` uses only `propext`,
`Classical.choice`, `Quot.sound`. Rechecked in a Lake build of the full
local-component determination proof (0 errors, 0 warnings).
