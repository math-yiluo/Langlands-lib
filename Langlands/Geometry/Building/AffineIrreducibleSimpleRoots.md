# Irreducible affine root systems and linear independence of simple affine roots

Module `Langlands.Geometry.Building.AffineIrreducibleSimpleRoots`, namespace
`Langlands.Geometry.Building.AffineRootSystem`.

## Contents

The module works with a set `Ψ : Set (A →ᵃ[ℝ] ℝ)` of affine functionals on a real affine
space `A` over `V` (independent universes `uV`, `uA`). In the main results `Ψ` is an actual
Library affine root system (`hΨ : IsAffineRootSystemWithRankZero Ψ`, the Library form of KP
axioms AR 1–AR 4), and a chamber is written `facet Ψ c` for a regular point `c`
(`hc : IsRegular Ψ c`: no root vanishes at `c`).

### Definitions

- `RootsOrthogonal Ψ Ψ₁ Ψ₂`: for every `ψ ∈ Ψ₁`, every `η ∈ Ψ₂` and all vectors `u, v`
  with `IsCoroot Ψ ψ u` and `IsCoroot Ψ η v`, both `ψ̇(v) = 0` and `η̇(u) = 0`. Here
  `IsCoroot Ψ ψ u` is the Library notion (`ψ̇(u) = 2` and the reflection `η ↦ η - η̇(u) ψ`
  preserves `Ψ`). For an affine root system every root has exactly one such vector, its
  coroot `ψ̇∨` (Library `exists_isCoroot` and `coroot_eq_of_linear_eq`), so this is KP's
  condition `ψ̇(η̇∨) = 0 = η̇(ψ̇∨)`.
- `IsIrreducibleRoots Ψ`: whenever `Ψ₁ ∪ Ψ₂ = Ψ` and `RootsOrthogonal Ψ Ψ₁ Ψ₂`, one of
  `Ψ₁, Ψ₂` is empty. For nonempty `Ψ` this is exactly "not reducible" in KP Definition
  1.3.13 (the parts `Ψ₁, Ψ₂` are automatically subsets of `Ψ`). KP defines
  (ir)reducibility only for nonempty `Ψ`; the empty set satisfies `IsIrreducibleRoots`
  vacuously, and nonemptiness is a separate hypothesis wherever it matters.
- `IsAffineRootSystemWithRankZero.corootBilin hΨ`: the Library coroot form `corootForm`
  (`(α, α') ↦ ∑ α(v) α'(v)` over the finite set of coroots) bundled as a bilinear map on
  `V*`; `corootBilin_apply` unfolds it.
- `IsAffineRootSystemWithRankZero.simpleDerivativeSpan T` for a set `T` of simple affine
  roots of `facet Ψ c`: the span in `V*` of their derivatives.

### Main result

- `IsAffineRootSystemWithRankZero.linearIndependent_simpleAffineRoots hΨ hirr hc`: if
  `hirr : IsIrreducibleRoots Ψ` and `hc : IsRegular Ψ c`, then the simple affine roots of the
  chamber `facet Ψ c` (Library `simpleAffineRoots Ψ (facet Ψ c)`) are linearly independent
  as affine functionals:
  `LinearIndependent ℝ (fun ψ : simpleAffineRoots Ψ (facet Ψ c) => (ψ : A →ᵃ[ℝ] ℝ))`.
  This is the linear-independence part of KP Proposition 1.3.22(5) ("Δ is a basis of
  `A*`"); spanning is not claimed. It is literally the hypothesis `hli` of the module
  `Langlands.Geometry.Building.AffineChamberVertexSimpleRoots` (KP Proposition 1.3.22(6)).
  No nonemptiness hypothesis is needed: for `Ψ = ∅` there are no simple roots.

### Intermediate results

For `hΨ`, `hc` as above and `T` a set of simple affine roots of `facet Ψ c`:

- `not_isIrreducibleRoots_of_split hΨ hc T hT hTc horth`: if `T` and its complement are
  both nonempty and the chamber Cartan matrix entry `chamberCartanMatrix Ψ (facet Ψ c) ψ η`
  (Library, `AffineChamberCartanMarks`) is `0` for all `ψ ∈ T` and `η ∉ T`, then `Ψ` is not
  irreducible. That is, an orthogonal splitting of the simple roots splits `Ψ`.
- `comp_linear_mem_simpleDerivativeSpan hΨ hc horth hw hα`: under the same orthogonality of
  `T` and its complement, every element `w` of the affine Weyl group `affineWeylGroup Ψ`
  pulls `simpleDerivativeSpan T` back into itself: `α ∈ span → α ∘ ẇ ∈ span`.
- `comp_reflection_mem_simpleDerivativeSpan`: the same for one simple reflection whose root is
  in `T` or whose coroot is killed by the derivatives of all roots in `T`.
- `corootForm_eq_zero_of_mem_span`: the coroot form vanishes on the spans of two sets of
  functionals that are pairwise orthogonal for it.
- With a `Fintype` instance on the simple roots:
  - `chamberCartanMatrix_eq_zero_of_nonneg_leftKernel`: if `y ≥ 0` is a real left-kernel
    vector of the Cartan matrix (`∑_ψ y_ψ ψ̇(η̇∨) = 0` for every simple `η`), `y_ψ ≠ 0` and
    `y_η = 0`, then the Cartan entry at `(ψ, η)` is `0`.
  - `exists_eq_smul_of_leftKernel`: for irreducible `Ψ` and a strictly positive real
    left-kernel vector `m`, every real left-kernel vector is a real multiple of `m`.

Auxiliary results without the root-system hypothesis:

- `comp_linear_mem_of_mem_closure`: if every generator of a subgroup of `A ≃ᵃ[ℝ] A` and its
  inverse pull a subspace `U ⊆ V*` back into itself, so does every element of the subgroup.
- `comp_affineReflection_linear`: pulling `α ∈ V*` back along the linear part of the
  affine reflection of `ψ` with `ψ̇(v) = 2` gives `α - α(v) ψ̇`.
- `linear_mem_simpleDerivativeSpan`: the derivative of a root in `T` lies in the span.

## Provenance

- `RootsOrthogonal` and `IsIrreducibleRoots` formalize Kaletha–Prasad, *Bruhat–Tits Theory:
  A New Approach* (2023), Definition 1.3.13 (printed p. 18, PDF p. 49): a non-empty affine
  root system `Ψ` is reducible if there exist non-empty subsets `Ψ₁, Ψ₂ ⊂ Ψ` that are
  orthogonal, `ψ̇(η̇∨) = 0 = η̇(ψ̇∨)` for every `ψ ∈ Ψ₁` and `η ∈ Ψ₂`, with
  `Ψ = Ψ₁ ∪ Ψ₂`; otherwise `Ψ` is irreducible. The differences are the ones described
  above: the coroot is quantified over all Library coroot vectors (there is exactly one),
  and the empty set is not excluded by the definition.
- `linearIndependent_simpleAffineRoots` is the linear-independence half of KP Proposition
  1.3.22(5) (printed p. 23, PDF p. 54): "Assume that Ψ is irreducible. (5) Δ is a basis of
  A*." KP Remark 1.3.24 (printed p. 24, PDF p. 55) explains that for reducible `Ψ` the set
  `Ψ(C)₀` is only generating, not linearly independent, which is why irreducibility is
  needed.
- KP's proof of 1.3.22(5) uses that the chamber is a simplex (KP Remark 1.3.16, citing
  Bourbaki through KP Lemma 1.3.14). The proof here takes a different, internal route through
  the chamber Cartan matrix and its positive integral marks (module
  `Langlands.Geometry.Building.AffineChamberCartanMarks`, the corrected form of KP
  Proposition 1.3.47): an orthogonal splitting of the simple roots splits `Ψ`, and
  otherwise the left kernel of the Cartan matrix, which contains the positive marks, is a
  line. This route and its intermediate results (invariance of derivative spans under the
  Weyl group, the splitting lemma, the kernel lemma) are internal.

## Proof notes

- **Weyl group invariance.** The affine Weyl group is generated by the simple reflections of
  the chamber: Library `affineReflectionGalleryGeometry` gives generation by the wall
  reflections of `c`, and `affineChamberWallComparison` identifies these with the simple
  reflections. A simple reflection of `δ` pulls `α` back to `α - α(δ̇∨) δ̇`
  (`comp_affineReflection_linear`). If `δ ∈ T` this stays in `simpleDerivativeSpan T`; if
  `δ ∉ T`, orthogonality says `ε̇(δ̇∨) = 0` for `ε ∈ T` (the Cartan entry, via
  `cast_chamberCartanMatrix`), so `α(δ̇∨) = 0` for `α` in the span. Simple reflections are
  involutions, so `comp_linear_mem_of_mem_closure` (induction over the subgroup closure)
  gives invariance under the whole group.
- **Splitting.** Let `T` and `Tᶜ` be nonempty and orthogonal (the Cartan zero pattern is
  symmetric, Library `chamberCartanMatrix_eq_zero_iff`). For a root `ψ` with coroot `u`,
  some simple `δ` has `δ̇(u) ≠ 0`; otherwise all `δ̇(u) ≥ 0` would force `u = 0`
  (`eq_zero_of_forall_simpleAffineRoots_linear_nonneg`), contradicting `ψ̇(u) = 2`. If `δ`
  lies in `T` (or in `Tᶜ`), invariance under `r_ψ` puts `δ̇ - δ̇(u) ψ̇` in the span of `T`
  (or of `Tᶜ`), hence `ψ̇` too. So `Ψ = Ψ₁ ∪ Ψ₂` with `Ψ₁, Ψ₂` the roots whose derivatives
  lie in the two spans. The coroot form vanishes between the spans
  (`corootForm_eq_zero_of_mem_span` and `chamberCartanMatrix_eq_zero_iff_corootForm`), and
  `2 corootForm(ψ̇, η̇) = ψ̇(η̇∨) corootForm(η̇, η̇)` with `corootForm(η̇, η̇) > 0`
  (`two_mul_corootForm`, `corootForm_self_pos`) turns this into `RootsOrthogonal Ψ Ψ₁ Ψ₂`.
  Both parts are nonempty, since they contain the simple roots in `T` and `Tᶜ`.
- **The left kernel.** Let `m > 0` and `y` be real left-kernel vectors. Put
  `z = y - (y_ψ₀ / m_ψ₀) m`, so `z_ψ₀ = 0`. By the Library lemma `abs_mem_leftKernel`,
  `|z|` is again in the left kernel. For `ψ` with `z_ψ ≠ 0` and `η` with `z_η = 0`, the
  `η`-th column sum `∑_θ |z_θ| θ̇(η̇∨) = 0` has nonpositive terms (the off-diagonal entries
  are `≤ 0`, `chamberCartanMatrix_nonpos`), so the `(ψ, η)` entry is `0`. If `z ≠ 0`,
  `T = {ψ | z_ψ ≠ 0}` and its complement (containing `ψ₀`) would split `Ψ`. So `z = 0`.
- **Linear independence.** Let `∑ b_ψ ψ = 0`. Taking derivatives and evaluating at the
  coroots shows that `b` is a left-kernel vector of the Cartan matrix. The integral marks
  `m > 0` of `exists_pos_vecMul_chamberCartanMatrix_eq_zero` give a positive one, so
  `b = t m`. Evaluating `∑ b_ψ ψ` at `c` gives `t ∑ m_ψ ψ(c) = 0`, and `∑ m_ψ ψ(c) > 0`
  because simple roots are positive on the chamber; hence `t = 0` and `b = 0`. The
  `Fintype` instance on the simple roots comes from `finite_simpleAffineRoots`.
