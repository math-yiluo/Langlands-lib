# The vertices of a chamber and its simple affine roots

Module `Langlands.Geometry.Building.AffineChamberVertexSimpleRoots`, namespace
`Langlands.Geometry.Building.AffineRootSystem`.

## Contents

The module works with an actual Library affine root system `Ψ : Set (A →ᵃ[ℝ] ℝ)` on a real
affine space `A` over `V` (`hΨ : IsAffineRootSystemWithRankZero Ψ`, the Library form of KP
axioms AR 1–AR 4). A chamber is written `facet Ψ c` for a regular point `c`
(`hc : IsRegular Ψ c`: no root vanishes at `c`), and its closure is the Library
`facetClosure Ψ c`. Universes are independent (`uV`, `uA`).

Most results take two further hypotheses:

- `hne : Ψ.Nonempty`. This excludes rank zero (`Ψ = ∅`), where the chamber has no simple
  affine roots and the correspondence is not meaningful.
- `hli : LinearIndependent ℝ (fun ψ : simpleAffineRoots Ψ (facet Ψ c) => (ψ : A →ᵃ[ℝ] ℝ))`:
  the simple affine roots are linearly independent as affine functionals. This is the
  linear-independence half of KP Proposition 1.3.22(5) ("Δ is a basis of A*"), which KP
  proves for irreducible `Ψ`. It is an explicit hypothesis here; the module does not derive
  it from irreducibility. For a reducible system it is false (KP Remark 1.3.24: then
  `Ψ(C)₀` is only generating), so the results are vacuous there, as they should be: the
  chamber of a reducible system is a product of simplices, and its vertices do not
  correspond to simple roots in this way.

### Definitions

- `simpleVertex Ψ C ψ : A` is a point at which every simple affine root of `C` other than
  `ψ` vanishes, chosen by `Classical.choice` when such a point exists, and an arbitrary point
  otherwise. Under the hypotheses above the point exists and is unique
  (`eq_simpleVertex_iff`), so the choice does not matter. It is the vertex `x_ψ` of
  KP Proposition 1.3.22(6), opposite to the wall of `ψ`.
- `IsAffineRootSystemWithRankZero.simpleVertexEquiv hΨ hli hc hne :
  simpleAffineRoots Ψ (facet Ψ c) ≃ {x : A // x ∈ facetClosure Ψ c ∧ IsVertex Ψ x}` is the
  bijection `ψ ↦ simpleVertex Ψ (facet Ψ c) ψ` (`coe_simpleVertexEquiv_apply`) between the
  simple affine roots and the vertices of the closed chamber. Here `IsVertex Ψ x` is the
  Library notion: the facet of `x` is `{x}`.

### Main results

For `hΨ`, `hli`, `hc`, `hne` as above and `ψ, η` simple affine roots of `facet Ψ c`:

- `exists_pos_linear_relation` (real marks): some `m` with every `m η > 0` has
  `∑ m_η η̇ = 0`, and `∑ m_η η(x) > 0` for every `x ∈ A`. So `∑ m_η η` is a positive
  constant. (This needs only a `Fintype` instance on the simple roots, `hli`, `hc`, `hne`.)
- `eq_simpleVertex_iff`: `x = simpleVertex Ψ (facet Ψ c) ψ` iff every simple root
  `η ≠ ψ` vanishes at `x`.
- `apply_simpleVertex_of_ne`, `apply_simpleVertex_pos`: `η(x_ψ) = 0` for `η ≠ ψ` and
  `ψ(x_ψ) > 0`. Together: KP's `ψ_i(x_j) = 0` for `i ≠ j` and `ψ_i(x_i) > 0`.
- `simpleVertex_mem_facetClosure`, `isVertex_simpleVertex`: `x_ψ` lies in the closure of the
  chamber and is a vertex.
- `simpleVertex_injOn`: distinct simple roots have distinct vertices.
- `exists_eq_simpleVertex_of_isVertex`: every vertex of the closed chamber is some `x_ψ`.
- `mem_facetClosure_and_isVertex_iff`: `x ∈ facetClosure Ψ c ∧ IsVertex Ψ x` iff
  `x = x_ψ` for some simple root `ψ`. With injectivity this is KP Proposition 1.3.22(6), and
  `simpleVertexEquiv` packages it as a bijection.
- `affineIndependent_simpleVertex`: the vertices `x_ψ` are affinely independent.
- `apply_simpleVertex` (naturality): for `e ∈ rootStabilizer Ψ` with
  `e '' facet Ψ c = facet Ψ c`, `e (x_ψ) = x_{ψ ∘ e⁻¹}`. (`comp_symm_mem_simpleAffineRoots`
  shows that `ψ ∘ e⁻¹` is again a simple root of the chamber.)
- `exists_mem_eq_comp_symm_of_subsingleton` (transitivity): let `Γ` be a subgroup of affine
  automorphisms of `A` with `Γ ≤ rootStabilizer Ψ` and `e '' facet Ψ c = facet Ψ c` for
  every `e ∈ Γ`. If the points of `facetClosure Ψ c` fixed by every element of `Γ` form a
  subsingleton, then for any two simple roots `ψ, η` some `e ∈ Γ` has `η = ψ ∘ e⁻¹`. This
  is the transitivity hypothesis of
  `IsAffineRootSystemWithRankZero.exists_perm_chamberCartanMatrix_apply_eq` in
  `Langlands.Geometry.Building.AffineChamberCartanMarks`.

Auxiliary results without the root-system hypothesis:

- `exists_forall_apply_eq_of_linearIndependent`: linearly independent functionals on a real
  vector space take any prescribed values at some vector.
- `affineMap_sum_apply`, `sum_mul_apply_eq_of_sum_smul_linear_eq_zero`,
  `eq_zero_of_linearIndependent_of_sum_eq_zero`, `smul_eq_smul_of_linearIndependent`,
  `linearIndependent_linear_ne`: for linearly independent affine functionals `f_i`, a
  relation `∑ a_i ḟ_i = 0` makes `∑ a_i f_i` constant; it is zero only if `a = 0`; any two
  such relations are proportional; and dropping one index in the support of a nonzero
  relation leaves linearly independent derivatives.
- `sum_mul_apply_eq_of_forall_ne`, `mul_nonneg_of_mem_facetClosure`,
  `symm_mem_rootStabilizer`, `symm_image_eq_of_image_eq`: small evaluation and sign facts.
- For `hΨ` and `hc` only: `eq_of_forall_simpleAffineRoots_apply_eq` (two points with equal
  values of all simple roots coincide), `simpleAffineRoots_nonempty` (a chamber of a
  nonempty system has a simple root), and `exists_ne_zero_linear_relation` (the derivatives
  of the simple roots satisfy a nontrivial linear relation).

## Provenance

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 1.3.22(5)–(6)
  (printed p. 23, PDF p. 54): for irreducible `Ψ`, `Δ = Ψ(C)₀` is a basis of `A*`, and "the
  vertices `{x₀, …, x_ℓ}` of `C` are in bijection with `Δ` specified by `ψ_i(x_j) = 0` if
  `i ≠ j` and `ψ_i(x_i) > 0`." The module proves (6) in the form of
  `mem_facetClosure_and_isVertex_iff`, `simpleVertex_injOn` and `simpleVertexEquiv`, with
  the linear-independence part of (5) as the explicit hypothesis `hli` in place of
  irreducibility. KP's proof uses that `C` is a simplex (Remark 1.3.16); the proof here
  derives what it needs from `hli` and the root-system axioms.
- The real marks (`exists_pos_linear_relation`) are the real-coefficient form of KP
  Proposition 1.3.47(1) (printed p. 31, PDF p. 62) as corrected in 2024 (corrections
  pp. 7–8: the combination is a non-zero constant). Only existence of positive real
  coefficients is claimed. Integral marks are in
  `IsAffineRootSystemWithRankZero.exists_pos_vecMul_chamberCartanMatrix_eq_zero`.
- The transitivity corollary formalizes a step in the proof of KP Theorem 10.3.1 (printed
  p. 392, PDF p. 423): there is "a natural Γ-equivariant bijective correspondence between
  the set of vertices of C and Δ", and since `B(G)` contains no facet of positive dimension,
  "we see from the discussion in 9.2.4 that Γ acts transitively on the set of vertices of C,
  and hence it acts transitively on Δ." The cited discussion in §9.2.4 (printed p. 327,
  PDF p. 358) is that the barycenter of a Γ-stable facet is Γ-fixed. Here the hypothesis is
  that the fixed points in the closed chamber form a subsingleton. The finite-simplex part is
  Worker 227's
  `exists_smul_eq_of_simplexFixedPointSubsingleton`
  (`Langlands.Geometry.Building.SimplexFixedPointTransitivity`). The rest (the action on
  simple roots, naturality, transfer from `A` to `V`) is internal glue.
- The linear-algebra lemmas are standard internal facts.

## Proof notes

- **A nontrivial relation.** If the derivatives `ψ̇` of the simple roots were linearly
  independent, some `v ∈ V` would have `ψ̇₀(v) = 1` and `η̇(v) = 0` for the other simple roots.
  Then all `η̇(v) ≥ 0`, so `v = 0` by the "no nonnegative direction" lemma
  `eq_zero_of_forall_simpleAffineRoots_linear_nonneg` of `AffineChamberCartanMarks`, a
  contradiction. (`hne` gives a simple root; otherwise every derivative would be `0`.)
- **Positive real marks.** Take a nonzero relation `∑ a_η η̇ = 0` and `ψ` with `a_ψ ≠ 0`. By
  `hli`, removing `ψ` leaves linearly independent derivatives (any relation not involving `ψ`
  is proportional to `a` and vanishes at `ψ`, so it is zero). If `a_η a_ψ ≤ 0` for some
  `η ≠ ψ`, choose `v` with `η̇(v) = 1` and `θ̇(v) = 0` for `θ ≠ ψ, η`; the relation forces
  `ψ̇(v) ≥ 0`, so all simple-root derivatives are `≥ 0` at `v ≠ 0`, again impossible. So
  `m_η = a_η a_ψ > 0`. Then `∑ m_η η` is constant, and its value at `c` is positive because
  every simple root is positive at `c`.
- **The vertex.** With `m`, removing `ψ` leaves linearly independent derivatives; choose `v`
  with `η̇(v) = -η(c)` for `η ≠ ψ`, and put `x_ψ = v + c`. Uniqueness: if `x, y` both kill
  all `η ≠ ψ`, then `m_ψ ψ(x) = ∑ m_η η(x) = ∑ m_η η(y) = m_ψ ψ(y)`, so all simple roots agree
  at `x` and `y`, and `x = y` by the "no nonnegative direction" lemma. Positivity:
  `m_ψ ψ(x_ψ) = ∑ m_η η(x_ψ) > 0`. Membership in the closure uses the Library criterion
  `mem_facetClosure_iff_simple_nonneg`. A point `y` in the facet of `x_ψ` has the same signs,
  so every `η ≠ ψ` vanishes at `y` and `y = x_ψ`; hence `x_ψ` is a vertex. Affine
  independence: applying `η̇` to a weighted difference `∑ w_ψ (x_ψ - x)` with `∑ w_ψ = 0`
  isolates `w_η η(x_η)`.
- **Every vertex is some `x_ψ`.** Let `x` be a vertex of the closed chamber. All simple roots
  are `≥ 0` at `x`, and `∑ m_η η(x) > 0`, so some `ψ₁(x) > 0`. If `x ≠ x_{ψ₁}`, some other
  simple root `ψ₂` is also positive at `x`. Put `u = x_{ψ₁} - x_{ψ₂}`: then `η̇(u) = 0` for
  every simple `η ≠ ψ₁, ψ₂`, and `ψ̇₁(u) = ψ₁(x_{ψ₁}) > 0`, so `u ≠ 0`. By local finiteness
  (`eventually_sign_smul_vadd`, `exists_pos_of_eventually`) there is `ε > 0` such that every
  root nonzero at `x` keeps its sign at `x ± εu`. Both points then lie in the closed chamber.
  A root `ζ` with `ζ(x) = 0` takes the values `±ε ζ̇(u)` there, and both must be on the
  closed side of `ζ(c) ≠ 0` (definition of `facetClosure`), so `ζ̇(u) = 0`. Hence `x + εu`
  has the same signs as `x` for all roots, so it is in the facet `{x}`, forcing `u = 0`, a
  contradiction.
- **Naturality.** `e` maps the simple roots of the chamber to themselves by `ψ ↦ ψ ∘ e⁻¹`
  (Library transport, `affineFunctionalTransport_mem_simpleAffineRoots_iff`). If `η ≠ ψ ∘ e⁻¹`
  then `η ∘ e ≠ ψ` is simple, so `η(e(x_ψ)) = (η ∘ e)(x_ψ) = 0`; uniqueness gives
  `e(x_ψ) = x_{ψ ∘ e⁻¹}`.
- **Transitivity.** `Γ` acts on the simple roots by `γ • ψ = ψ ∘ γ⁻¹`. Transfer to `V` by
  `x ↦ x - c`: the points `p_ψ = x_ψ - c` are affinely independent, `γ` acts on `V` by
  `v ↦ γ(v + c) - c` and maps `p_ψ` to `p_{γ • ψ}`. The convex hull of the `p_ψ` lies in the
  translate of the closed chamber (it is convex, by the simple-root criterion). So the
  fixed points of `Γ` in the hull form a subsingleton, and Worker 227's
  `exists_smul_eq_of_simplexFixedPointSubsingleton` gives transitivity.
