# Weak approximation at finitely many finite places and all infinite places

Author: Worker 226.

Let `K` be a number field and `S` a finite set of finite places of `K` (height-one primes of
`𝓞 K`). This module proves weak approximation for the places in `S` together with all
infinite places of `K`. It also proves the idele form used in the proof of Artin–Tate,
*Class Field Theory* (2009), Chapter V §4, Theorem 2, printed p.17 (PDF p.26): "We can find
`α ∈ k` such that `α⁻¹a` is so close to `1` at all `p ∈ S` that …". In that proof `S` may
contain archimedean places. The theorem here imposes conditions at the finite places in `S`
and at every infinite place, which covers the archimedean places of any such `S`. Everything
is in namespace `Langlands.Global.AdelicFunctoriality`, with `K : Type u`.

## The family of absolute values

- `mixedAbv S : S ⊕ InfinitePlace K → AbsoluteValue K ℝ` sends a finite place `p ∈ S` to
  Mathlib's normalized `p`-adic absolute value `NumberField.HeightOneSpectrum.adicAbv K p` and
  an infinite place `w` to its underlying absolute value `w.1`.
- `mixedAbv_isNontrivial`: every member is nontrivial. The finite case is the Library's
  `finiteAdicAbv_isNontrivial` (module `FiniteComparisonReduction`). The infinite case is
  Mathlib's `InfinitePlace.isNontrivial`.
- `finiteAdicAbv_not_isEquiv_infinitePlace`: the `p`-adic absolute value is not equivalent to
  the absolute value of an infinite place. The `p`-adic absolute value of the integer `2` is
  at most `1` (Mathlib's `adicAbv_natCast_le_one`). An infinite place takes the value `2` at
  `2` (`InfinitePlace.map_natCast`). Equivalent absolute values agree on which elements have
  absolute value at most `1`, so these two cannot be equivalent.
- `mixedAbv_pairwise_not_isEquiv`: distinct indices give inequivalent absolute values. Two
  finite places use the Library's `finiteAdicAbv_isEquiv_iff`. Two infinite places use
  Mathlib's `InfinitePlace.eq_iff_isEquiv`. Mixed pairs use the previous lemma, applied once
  directly and once to the symmetric equivalence.
- `denseRange_algebraMap_mixedAbv`: `K` has dense image in the product of the spaces
  `WithAbs (mixedAbv S i)`. This is Mathlib's abstract weak approximation theorem
  `AbsoluteValue.denseRange_algebraMap_pi` applied to the finite family above.

## Approximation in the completions

- `exists_algebraMap_mem_open`: let `A p` be a nonempty open subset of `p.adicCompletion K` for
  each `p ∈ S`, and let `B w` be a nonempty open subset of `w.Completion` for each infinite
  place `w`. Then some `x : K` has `algebraMap K (p.adicCompletion K) x ∈ A p` for every
  `p ∈ S` and `algebraMap K w.Completion x ∈ B w` for every `w`.

  Proof. Pull `A p` back along the Library's isometric dense embedding
  `finiteWithAbsEmbedding p : WithAbs (adicAbv K p) → p.adicCompletion K`. Pull `B w` back
  along Mathlib's continuous dense coercion `WithAbs w.1 → w.Completion`. The preimages are
  open by continuity and nonempty by density (`DenseRange.exists_mem_open`). Their product
  over the finite index type is open (`isOpen_set_pi`) and nonempty, so it meets the dense
  image of `K`. The coordinates of the resulting element reduce by definition to the two
  embeddings of `x`.

## The idele form

- `isOpen_image_val_inv_mul_mem`: in a topological division ring `F` that is a field and a
  `T1Space`, the set of values `(u : F)` of units `u` with `u⁻¹ * c ∈ interior U` is open, for
  any unit `c` and any `U : Set Fˣ`. The proof shows that the coercion `Fˣ → F` is an open
  embedding. It is an embedding by Mathlib's `Units.isEmbedding_val₀`, and its range is the
  open set `{0}ᶜ`. The defining condition on `u` is open because `u ↦ u⁻¹ * c` is
  continuous.
- `mem_image_val_inv_mul_mem`: if `U` is a neighbourhood of `1`, then `c` itself lies in that
  set, since `c⁻¹ * c = 1` lies in the interior of `U`.
- `exists_principal_inv_mul_mem S a U hU V hV`: take an idele `a : IdeleGroup (𝓞 K) K`, sets
  `U p ⊆ (p.adicCompletion K)ˣ` with `U p ∈ 𝓝 1` for every `p ∈ S`, and sets
  `V w ⊆ (w.Completion)ˣ` with `V w ∈ 𝓝 1` for every infinite place `w`. Then there is
  `α : Kˣ` such that the `p`-coordinate (`ideleCoordinate`) of `(unitEmbedding α)⁻¹ * a` lies
  in `U p` for every `p ∈ S`, and its `w`-coordinate (`ideleInfiniteCoordinate`) lies in
  `V w` for every infinite place `w`. No condition is imposed at finite places outside `S`.
  The sets `U p` for `p ∉ S` are not used.

  Proof. Apply `exists_algebraMap_mem_open` to the open sets of the two previous lemmas,
  formed with `c` the coordinate of `a` at `p` or `w`. Neither set contains `0`, and `K` has
  an infinite place, so the resulting `x` is nonzero. Put `α = Units.mk0 x _`. At each place,
  the coordinate of the principal idele of `α` is the unit `u` produced by the image condition
  (`ideleCoordinate_unitEmbedding`, `ideleInfiniteCoordinate_unitEmbedding` and `Units.ext`).
  The coordinate maps are monoid homomorphisms, so the coordinate of
  `(unitEmbedding α)⁻¹ * a` is `u⁻¹ * c`. This lies in the interior of the prescribed set,
  hence in the set.

The conclusion of `exists_principal_inv_mul_mem` has exactly the shape of the hypothesis
`hadjust` in the draft for task 275d5e34 (`AlmostEverywhereSplitNormProof`), once
`U p` and `V w` are the ranges of the local norms. Showing that these ranges are
neighbourhoods of `1` is a separate result that is not proved here.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
