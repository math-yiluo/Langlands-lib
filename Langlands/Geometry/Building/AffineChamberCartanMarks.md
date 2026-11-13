# The Cartan matrix and the marks of the simple affine roots of a chamber

Module `Langlands.Geometry.Building.AffineChamberCartanMarks`, namespace
`Langlands.Geometry.Building.AffineRootSystem`.

## Contents

The module works with an actual Library affine root system
`Ψ : Set (A →ᵃ[ℝ] ℝ)` on a real affine space `A` over `V`, with
`hΨ : IsAffineRootSystemWithRankZero Ψ`. This is the Library form of axioms AR 1–AR 4 of
Kaletha–Prasad, Definition 1.3.1, with AR 4 as corrected in 2024 and AR 1 in a
derivative-spanning form that also allows rank zero. It assumes no irreducibility and no marks. Universes
are independent (`uV`, `uA`, and `uW`, `uB` for the second space in the transport
section).

### Definitions

- `corootVector Ψ ψ : V` is a vector `v` with `IsCoroot Ψ ψ v` (`ψ̇(v) = 2` and
  `η - η̇(v) ψ ∈ Ψ` for all `η ∈ Ψ`, AR 2), chosen by `Classical.choice` when one exists and
  `0` otherwise. For `ψ ∈ Ψ` it is a coroot (`isCoroot_corootVector_of_mem`), and it is the
  only one (`corootVector_eq`, from the Library uniqueness `coroot_eq_of_linear_eq`). So
  the choice does not affect any value below. This is the coroot `ψ∨` of KP.
- `chamberCartanMatrix Ψ C : Matrix (simpleAffineRoots Ψ C) (simpleAffineRoots Ψ C) ℤ`
  has entry `⌊ψ̇(η∨)⌋` at `(ψ, η)`. Here `simpleAffineRoots Ψ C` is the Library set of
  simple affine roots of `C`: positive on `C`, not divisible, and with a wall of `C` as
  zero set. For a root system this matches KP's basis `Ψ(C)₀`. The rows and columns are
  indexed by the simple roots themselves. By AR 3, `ψ̇(η∨)` is an integer
  (`cast_chamberCartanMatrix`), so the floor only changes the type from `ℝ` to `ℤ`. The
  matrix has the integers `ψ(η∨)` that KP's Construction 1.3.64 uses to draw the affine
  Dynkin diagram, where `f(ψ, η) = ψ(η∨) · η(ψ∨)`.
- `simpleAffineRootsEquivOfTransport e h hD : simpleAffineRoots Ψ C ≃ simpleAffineRoots Φ D`
  is the bijection `ψ ↦ ψ ∘ e⁻¹` (`affineFunctionalTransport e`). Here `e : A ≃ᵃ[ℝ] B` is
  an affine equivalence, `h : transportedRoots e Ψ = Φ`, and `hD : e '' C = D`.

### Main results

For `hΨ : IsAffineRootSystemWithRankZero Ψ`:

- `chamberCartanMatrix_self`: the diagonal entries are `2`.
- `chamberCartanMatrix_nonpos`: for a regular point `c` (no root vanishes at `c`), the
  off-diagonal entries of the Cartan matrix of the chamber `facet Ψ c` are `≤ 0`.
- `chamberCartanMatrix_eq_zero_iff`: the zero pattern is symmetric. An entry `(ψ, η)` is
  zero exactly when `ψ̇` and `η̇` are orthogonal for the Library's invariant coroot form
  (`chamberCartanMatrix_eq_zero_iff_corootForm`).
- `eq_zero_of_forall_simpleAffineRoots_linear_nonneg`: a vector `v ∈ V` with `ψ̇(v) ≥ 0` for
  every simple affine root of a chamber is `0`.
- `abs_mem_leftKernel`: if a real vector `y` satisfies `∑ψ y_ψ ψ̇(η∨) = 0` for every `η`,
  then so does `|y|`.
- `exists_pos_vecMul_chamberCartanMatrix_eq_zero` (the marks): if the simple affine roots of
  the chamber `facet Ψ c` form a finite type, some `m : simpleAffineRoots Ψ (facet Ψ c) → ℤ`
  has every `m ψ > 0` and `m ᵥ* chamberCartanMatrix Ψ (facet Ψ c) = 0`, that is
  `∑ψ m_ψ ψ̇(η∨) = 0` for every simple root `η`.
- `chamberCartanMatrix_spec`: for every chamber `C` (`IsChamber Ψ C`) with
  `[Fintype (simpleAffineRoots Ψ C)]`, the Cartan matrix has diagonal entries `2`,
  off-diagonal entries `≤ 0` and a symmetric zero pattern, and it has a left-kernel vector
  with strictly positive integer entries.

Transport and automorphism covariance:

- The imported `hyperplane_affineFunctionalTransport` from `AffineFacetTransport`,
  together with `isFaceOf_image_iff_transportedRoots`,
  `isChamberWall_transportedRoots_iff`, `affineFunctionalTransport_mem_simpleAffineRoots_iff`
  and `simpleAffineRoots_transportedRoots` show that transport along `e` matches zero sets,
  faces, chamber walls and simple affine roots:
  `simpleAffineRoots (transportedRoots e Ψ) (e '' C) = affineFunctionalTransport e '' simpleAffineRoots Ψ C`.
- `IsAffineRootSystemWithRankZero.chamberCartanMatrix_transport`: the entries are preserved,
  `chamberCartanMatrix Φ D (σ ψ) (σ η) = chamberCartanMatrix Ψ C ψ η`, where
  `σ = simpleAffineRootsEquivOfTransport e h hD`.
- `transportedRoots_eq_self_of_mem_rootStabilizer`: an `e ∈ rootStabilizer Ψ` has
  `transportedRoots e Ψ = Ψ`.
- `IsAffineRootSystemWithRankZero.exists_perm_chamberCartanMatrix`: an `e ∈ rootStabilizer Ψ`
  with `e '' C = C` gives a permutation `σ` of `simpleAffineRoots Ψ C` with
  `σ ψ = ψ ∘ e⁻¹` that preserves every entry of the chamber Cartan matrix.
- `IsAffineRootSystemWithRankZero.exists_perm_chamberCartanMatrix_apply_eq`: take
  `Γ ⊆ rootStabilizer Ψ` with every element stabilizing `C`, and suppose that for any two
  simple affine roots `ψ, η` some `e ∈ Γ` has `η = ψ ∘ e⁻¹`. Then for any `ψ, η` some
  permutation of the simple affine roots preserves all entries of the Cartan matrix and
  sends `ψ` to `η`. This is the form of the matrix transitivity condition used for the
  affine diagram shape: the Cartan matrix is vertex-transitive.

## Provenance

The definitions are derived from the literature. They are not verbatim transcriptions.

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Construction 1.3.64 (printed
  p. 39, PDF p. 70), builds the affine Dynkin diagram of an irreducible affine root system
  from a chamber `C`. Its nodes are the elements of `Ψ(C)₀` and its bonds come from the
  integers `ψ(η∨)`. `chamberCartanMatrix` records exactly these integers as a matrix indexed
  by `Ψ(C)₀`. It does not use irreducibility, and it does not form bonds or arrows.
- KP Proposition 1.3.47 (printed p. 31, PDF p. 62), with the authors' 2024 corrections
  (pp. 7–8: "non-zero constant functional", "without common factor", and a replaced proof
  of (2)), gives for irreducible `Ψ` positive integers `n_ψ` with `∑ n_ψ ψ` a nonzero
  constant. Then `∑ n_ψ ψ̇ = 0`, so `(n_ψ)` is a positive integral left-kernel vector of the
  Cartan matrix. `exists_pos_vecMul_chamberCartanMatrix_eq_zero` proves this left-kernel
  conclusion directly for every affine root system, irreducible or not. It claims only
  existence: no primitivity, no uniqueness, no positivity of the constant, and not the
  stronger statement that `∑ m_ψ ψ` is constant.
- The transport results are internal glue that combine the Library's root transport
  (`transportedRoots`, `affineFunctionalTransport`, `isCoroot_transport_iff`,
  `IsAffineRootSystemWithRankZero.transport`) with the definitions above. They formalize
  the standard fact that an automorphism of `(A, Ψ)` fixing a chamber permutes its simple
  roots and preserves the integers `ψ(η∨)`.

## Proof notes

- **Integrality and diagonal.** AR 3 (`coroot_integral`) gives `ψ̇(η∨) ∈ ℤ`. The diagonal is
  `ψ̇(ψ∨) = 2`.
- **Sign and zero pattern.** The Library identity
  `2 β(ψ̇, η̇) = ψ̇(η∨) β(η̇, η̇)` for the invariant coroot form `β` (`two_mul_corootForm`),
  with `β(η̇, η̇) > 0`, turns statements about the entries into statements about `β`. Then
  symmetry of `β` gives the symmetric zero pattern. For the sign, each simple affine root is
  a positive multiple of a chamber simple root of the Library
  (`exists_eq_smul_chamberSimpleRoot`), and the Library shows that their Gram entries are
  `≤ 0` (`chamberSimpleGram_nonpos`). Two distinct simple roots of one chamber are never
  positive multiples of each other (`eq_of_mem_simpleAffineRoots_of_eq_smul`, using
  non-divisibility), so distinct simple roots give distinct chamber simple roots.
- **No nonnegative direction.** Suppose `ψ̇(v) ≥ 0` for every simple root and `v ≠ 0`. The
  derivatives of the roots span `V*`, so some root has nonzero derivative at `v`. Replacing
  it by its negative if needed gives a root `ξ₀` with `ξ̇₀(v) < 0`. A point lies in the
  chamber `facet Ψ c` exactly when every simple root is positive there (the Library's
  `facetRel_iff_simple_pos`). So every point `c + t v` with `t ≥ 0` stays in the chamber.
  Hence every root `ξ` with `ξ̇ = ξ̇₀` is negative at `c`: if `ξ(c) > 0`, then `ξ` would be
  negative at `c + t v` for large `t`, a change of sign inside the chamber. Apply this also
  to `-(ξ - ξ̇(u₀) ξ₀) ∈ Ψ`, where `u₀` is a coroot of `ξ₀` and `ξ̇(u₀) = 2`. That root has
  derivative `ξ̇₀` too, and the result is `2 ξ₀(c) < ξ(c) < 0`. So
  `|ξ(x) - ξ₀(x)| ≤ |ξ₀(c)|` for all `x`. By the no-accumulation half of AR 4
  (`finite_bounded`) this set of roots is finite. That contradicts the other half of AR 4
  (`infinite_fiber`).
- **Absolute values (Perron–Frobenius step).** For a real left-kernel vector `y`, put
  `g = ∑ y_ψ ψ̇`. The coroot form gives `β(η̇, g) = 0` for every simple `η`, hence
  `β(g, g) = 0`. So `g` vanishes on every coroot, and `y` is an isotropic combination in the
  sense of the Library (`IsIsotropicCombination`). The Library lemma
  `IsIsotropicCombination.abs` then shows that `|y|` is one too, using that the off-diagonal
  Gram entries are `≤ 0`.
- **Marks.** `exists_pos_int_vecMul_eq_zero` is a Stiemke-type alternative over `ℚ` for an
  integer matrix `M` with two properties: its rational left kernel is closed under absolute
  values, and `M x ≥ 0` forces `M x = 0`. For each index `i`, no `x` has `M x = e_i`, so
  rational duality (`Submodule.exists_dual_map_eq_bot_of_notMem`) gives a rational
  left-kernel vector `y⁽ⁱ⁾` with `y⁽ⁱ⁾_i ≠ 0` (`exists_vecMul_eq_zero_apply_ne_zero`). The sum
  `∑ᵢ |y⁽ⁱ⁾|` is a strictly positive rational left-kernel vector. Clearing denominators
  (`exists_nat_mul_eq_intCast`) makes it integral. For the Cartan matrix, the hypothesis
  `M x ≥ 0 ⇒ M x = 0` comes from the "no nonnegative direction" lemma applied to
  `v = ∑ x_η η∨`, since `ψ̇(v) = (M x)_ψ`. The abs-closure comes from the previous step.
- **Covariance.** Transport sends coroots to coroots (`isCoroot_transport_iff`), so
  `corootVector Φ (ψ ∘ e⁻¹) = e.linear (corootVector Ψ ψ)` by uniqueness. Then
  `(ψ ∘ e⁻¹)˙(e.linear η∨) = ψ̇(η∨)`. The zero set, face, wall and simple-root lemmas show
  that the bijection lands in the simple roots of `e '' C`.
