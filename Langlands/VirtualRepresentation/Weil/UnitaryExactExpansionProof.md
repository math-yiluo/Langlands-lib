# Effective unitary exact expansion

Author: Worker 981.

This module proves the published statement
`Langlands.VirtualRepresentation.Weil.EffectiveUnitaryExactExpansionStatement.{uG,uV} G`
and its specialization to the actual local Weil group. The proved theorems are:

- `Weil.effectiveUnitaryExactExpansion G : EffectiveUnitaryExactExpansionStatement.{uG, uV} G`
- `LocalWeil.effectiveUnitaryExactExpansion F : LocalWeil.EffectiveUnitaryExactExpansionStatement.{uF, uW} F`

In the generic theorem, `G : Type uG` is arbitrary with only `[Group G]` and
`[TopologicalSpace G]`. The carrier universe `uV` is independent. In the local
theorem, `p` is any prime (`[Fact p.Prime]`) and `F : Langlands.PadicField.{uF} p`
is arbitrary. The carrier universe `uW` is independent. There are no other
hypotheses.

The statement says the following. Let `A : FiniteRepresentation.{0, uG, uV} ℂ G`
be continuous (`hc : A.IsContinuous`) and have an invariant positive definite
Hermitian form (`A.IsUnitary`). Then some `x : Weil.UnitaryLattice G` has all
coefficients nonnegative (`x ∈ VirtualRepresentation.effective`) and satisfies
`Weil.ExactExpansion G (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩)
(includeUnitary G x)`. So `realizeExact G (includeUnitary G x)` is the whole
exact class of `A`. The exact quotient, the realization map and the unitary
basis are the published ones, unchanged. The unitary basis consists of the
genuine continuous irreducible classes of positive rank that have an
invariant positive Hermitian form.

## Route

The proof uses composition factors, not a direct-sum decomposition. Take any
composition series of `A`. Each graded factor is a quotient of an invariant
subspace of `A`. We show that each factor is again unitary. Its basis class
then lies in the unitary basis. The sum of these unitary generators has
nonnegative coefficients. Its image in the full irreducible lattice is the
published composition-series sum `seriesSum`. The published
`realizeExact_seriesSum` already identifies the realization of `seriesSum`
with the exact class of `A`.

## Unitary subquotients (namespace `Langlands.FiniteRepresentation`)

- `exists_sub_mem_orthogonal`: let `V` be a finite-dimensional complex vector
  space with a positive definite Hermitian form `h : InnerProductSpace.Core ℂ V`,
  and let `K` be a subspace. Every `v` has some `k ∈ K` with `v - k` orthogonal
  to `K`. The proof builds the normed group and inner product space from the
  core locally. A finite-dimensional `K` is complete
  (`FiniteDimensional.complete`). Mathlib's
  `Submodule.HasOrthogonalProjection.exists_orthogonal` then gives `k`.
- `orthogonalSubrepresentation b S`: for an invariant positive form `b` and a
  subrepresentation `S`, the vectors orthogonal to `S` under `b` form a
  subrepresentation. Linearity of the form in its second argument gives the
  submodule axioms. Invariance holds because `S` is stable under `ρ g⁻¹`. We
  rewrite `u` as `ρ g (ρ g⁻¹ u)` and apply invariance:
  `b(u, ρ g v) = b(ρ g⁻¹ u, v) = 0`. This is where invertibility of the group
  action is used.
- `isUnitary_of_injective_intertwiner`: an injective intertwiner into a unitary
  representation makes the source unitary. The proof goes through the published
  `isUnitary_iff_isUnitarizable` and `IsUnitarizable.of_injective`.
- `isUnitary_subrepresentation`: every subrepresentation of a unitary
  representation is unitary. Apply the previous lemma to the subspace inclusion.
- `isUnitary_of_surjective_intertwiner`: a surjective intertwiner
  `q : A → B` from a finite-dimensional unitary `A` makes `B` unitary. Fix an
  invariant positive form `b` on `A` and let `C` be the orthogonal
  subrepresentation of `ker q`. The restriction of `q` to `C` is bijective:
  - Injective: if `x, y ∈ C` have the same image, then `x - y` lies in both
    `ker q` and `C`. So it is orthogonal to itself, and definiteness gives
    `x - y = 0`.
  - Surjective: write `w = q v` and choose `k ∈ ker q` with `v - k ∈ C` by
    `exists_sub_mem_orthogonal`. Then `q (v - k) = q v`.

  Mathlib's `IntertwiningMap.ofBijective` turns this into an equivalence of
  representations from `C` to `B`. Finally `C` is unitary by
  `isUnitary_subrepresentation`, so the published `isUnitary_of_equiv`
  transfers unitarity to `B`.
- `isUnitary_continuousFiltrationGraded`: for every finite filtration `s` of a
  continuous unitary object `A`, each published graded quotient
  `continuousFiltrationGraded A s i` is unitary. That quotient is the image of
  the surjective `s.gradedProjection i` from the subrepresentation
  `s.subrepresentation i.succ`. Apply the two previous lemmas.

No topological-group hypothesis is needed. Continuity of the factors is
already part of the published `continuousFiltrationGraded`.

## Unitary lattice bookkeeping (namespace `Langlands.VirtualRepresentation.Weil`)

- `basisOf_mem_unitarySet`: the published basis class `basisOf B h` of a
  continuous irreducible unitary object `B` lies in `unitarySet G`. The witness
  is `B.val` itself, since the published `IsUnitaryClass` asks for a unitary
  representative of the underlying class.
- `includeUnitary_generator`: `includeUnitary` sends the generator of a unitary
  basis element `b` to the generator of `b.val`.
- `generator_mem_effective`: every lattice generator has nonnegative
  coefficients.
- `unitarySeriesSum A s hs hu`: the unitary-lattice sum over `i : Fin n` of the
  generators of the unitary basis classes of the graded factors. Here `hs` says
  the factors are irreducible and `hu` says they are unitary.
- `unitarySeriesSum_mem_effective`: this sum is effective, because effective
  elements form an additive submonoid.
- `includeUnitary_unitarySeriesSum`: its image under `includeUnitary` is the
  published `seriesSum A s hs`. Expand both sums and apply linearity together
  with `includeUnitary_generator`.

## Closing theorems

`Weil.effectiveUnitaryExactExpansion` takes `A`, `hc` and the unitarity proof.
The published `ExactCoefficients.exists_series` gives a composition series `s`
of `⟨A, hc⟩` with simple factors `hs`. `isUnitary_continuousFiltrationGraded`
shows that every factor is unitary. The witness is
`x = unitarySeriesSum ⟨A, hc⟩ s hs _`, which is effective by
`unitarySeriesSum_mem_effective`. Then
`realizeExact G (includeUnitary G x) = realizeExact G (seriesSum ⟨A, hc⟩ s hs)`
by `includeUnitary_unitarySeriesSum`. The published
`realizeExact_seriesSum` (from `ExactRealizationProof`) identifies the right
side with the exact class of `⟨A, hc⟩`. This is exactly the required
`ExactExpansion`.

The zero representation needs no separate case. Its composition series has
length `0`, so the witness is the empty sum, the zero lattice element.

`LocalWeil.effectiveUnitaryExactExpansion` applies the reverse direction of
the published `LocalWeil.effectiveUnitaryExactExpansion_iff` to the generic
theorem at `Langlands.Weil.Local.localWeilGroup F`. That equivalence is
definitional: it uses the existing local unitary lattice, inclusion, exact
group and expansion relation.

## Scope and provenance

This is internal derived finite-dimensional mathematics. No new literature
claim is made. The application context is Henniart 2000, §2.5 (source
`henniart-2000-simple-proof`). There the class of the full local restriction
`S_{v0}`, a continuous unitary representation of the local Weil group that is
in general reducible, is used in the free integer module on continuous
irreducible classes. The statement's paired Markdown records those source
conventions.

The proof uses neither semisimplicity nor the bijectivity of `realizeExact`. It
also makes no claim about uniqueness of the expansion, an isometry, lattice
spanning, global witnesses or a local Langlands correspondence.
