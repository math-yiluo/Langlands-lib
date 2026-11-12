# `L²(G, χ, dg*)₀` is the space of smooth vectors of its Hilbert completion

Author: Worker 1222. Module
`Langlands.Representation.MatrixCoefficient.CentralL2SmoothVectorsStatement`, namespace
`Langlands.Renard.CompactRepresentation`. Statement `CentralL2SmoothVectorsStatement : Prop`
(universe parameter `uG`); nothing is proved here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, IV.3.1, the Remark after the Definition, printed p.99 / PDF p.105. The registered
source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation:

> The space `L²(G, χ, dg*)₀` is the space of smooth vectors in its Hilbert completion
> `L²(G, χ, dg*)`.

The setting of IV.3.1: `G` is unimodular, `dg*` is a bi-invariant Haar measure on `G/Z(G)`,
`χ` is a unitary character of `Z(G)`, and `L²(G, χ, dg*)₀` consists of the functions `f` with
`f(gz) = χ(z) f(g)` and `∫_{G/Z(G)} |f|² dg* < ∞`, with the right regular representation and
the invariant positive definite form `⟨f₁, f₂⟩ = ∫_{G/Z(G)} conj(f₁(g)) f₂(g) dg*`.

## The published objects

- `Induction.CentralL2 χ hχ μ` (module `Langlands.Representation.MatrixCoefficient.CentralL2`,
  Worker 88) is the Library's `L²(G, χ, dg*)₀`: centrally covariant functions with a uniform
  open right stabilizer whose quotient norm is square integrable for `μ`, with the right
  translation representation `centralL2Representation`.
- `Induction.centralL2Form χ hχ μ` is the published `InvariantPositiveForm` of that
  representation, the integral over `G/Z(G)` of `conj(f₁) f₂`.
- For an invariant positive form `b`, `b.HilbertCompletion` is Mathlib's completion of the
  carrier normed by `b`, `b.toHilbert` is the canonical dense embedding, and
  `b.completedRepresentation` is the action extended by continuity (module
  `Langlands.Representation.Unitary.Completion`). This is Renard's Hilbert completion
  `L²(G, χ, dg*)` with its unitary action.
- `smoothVectors σ` is the published submodule of vectors fixed by some open subgroup.

## Statement

The statement quantifies over a t.d. group `G : Type uG` (`[Group G] [TopologicalSpace G]
[IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]`), a
character `χ : Subgroup.center G →* ℂˣ` with `hχ : ∀ z, ‖χ z‖ = 1`, and a Borel Haar measure
`μ` on `G ⧸ Subgroup.center G` that is also right invariant (Renard's bi-invariant `dg*`, as
in the published IV.3 statements). With `b := Induction.centralL2Form χ hχ μ` it asserts: for
every `w : b.HilbertCompletion`,

`w ∈ smoothVectors b.completedRepresentation ↔ ∃ f : Induction.CentralL2 χ hχ μ, b.toHilbert f = w`.

That is, the smooth vectors of the completion are exactly the (image of the) elements of
`L²(G, χ, dg*)₀`.

## Faithfulness notes

- Renard defines `L²(G, χ, dg*)₀` inside `𝒞^∞(G)`, which in II.1.2 (printed p.30 / PDF p.36) is the space of locally
  constant functions. Read literally, that space can contain functions that are locally
  constant but have no open right stabilizer. For example, take `χ` trivial and
  `G = SL_2(F)`, compact open subgroups `K_n` shrinking to `{1}`, and elements `g_n` tending to
  infinity so that the sets `g_n K_n Z(G)` are pairwise disjoint and form a locally finite
  family. Then `f = Σ c_n 1_{g_n K_n Z(G)}` with all `c_n ≠ 0` and `Σ |c_n|² vol < ∞` is
  locally constant, `Z(G)`-invariant and square integrable modulo `Z(G)`, but no open subgroup
  fixes it under right translation. Such an `f` is not a smooth vector of the completion, so
  the Remark needs `L²(G, χ, dg*)₀` to consist of smooth vectors
  of the right regular representation. The source supports this reading: IV.3.1 calls
  `(L²(G, χ, dg*)₀, r)` a unitary representation, and unitary representations are smooth by
  the Definition of IV.2.2. The published `CentralL2` follows this reading, and the statement
  is about it.
- The Hilbert completion is the abstract completion of `(L²(G, χ, dg*)₀, b)`. Renard's
  `L²(G, χ, dg*)` is that completion; no identification with a space of almost-everywhere
  classes of functions is asserted.
- `G` is not assumed unimodular separately: the published IV.3 statements express Renard's
  assumption through a Haar measure on `G/Z(G)` that is also right invariant, and so does this
  statement.

## Remaining obligations

The proof is a separate obligation. Elements of `L²(G, χ, dg*)₀` are smooth vectors because
the completed operators extend the original ones. Conversely, if an open subgroup fixes `w`,
it contains a compact open subgroup `K` fixing `w`; averaging over `K` is a continuous
projector of the completion that maps `L²(G, χ, dg*)₀` onto its `K`-fixed functions and fixes
`w`, and one shows that the `K`-fixed part of `L²(G, χ, dg*)₀` is closed in the completion
(its elements are determined by their values on the cosets `gK`). None of this is asserted
here.

## Provenance

Source assertion of Renard 2026, IV.3.1, Remark (printed p.99 / PDF p.105), stated for the
published model `Induction.CentralL2` of `L²(G, χ, dg*)₀` (smooth-vector reading, see above),
its published invariant form, and the published Hilbert completion with its completed action.
