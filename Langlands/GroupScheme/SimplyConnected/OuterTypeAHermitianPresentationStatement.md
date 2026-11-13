# An all-test Hermitian matrix presentation of outer type A groups

Author: Worker 195.

Module: `Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianPresentationStatement`.

`Langlands.GroupScheme.OuterTypeAHermitianPresentationStatement.{u}` is a
prerequisite statement for the outer type A part of the local rank-one
classification (Task 5813, `OuterTypeARankOneHermitianStatement`). It is not
proved here. It says that a simply connected group of absolute type `A_n`
whose star action is the reversal of the Dynkin chain and whose two end
vertices are distinguished is the special unitary group of a nonsingular
Hermitian matrix over a separable quadratic extension. The identification is
given on every test scheme by actual matrices, naturally, and the maximal
split torus acts through diagonal matrices with explicit characters. It does
not compute the Witt index of the Hermitian matrix and does not construct a
representing scheme for the unitary group.

## The statement

The statement quantifies over a field `K : Type u`, a group scheme `G` over
`Spec K` with affine structure morphism and locally of finite type, actual
index data `d : TitsIndexData G`, a natural number `n` and a bijection
`e : d.Vertex ≃ Fin n`. It assumes:

- `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`;
- every actual Cartan pairing `d.cartan a b` equals
  `CartanMatrix.A n (e a) (e b)` (absolute type `A_n`; Mathlib's matrix has
  `n` rows);
- `d.StarImagePair e Fin.revPerm`: the full absolute Galois star action,
  read through `e`, is either the identity or the reversal `i ↦ n - 1 - i`,
  and the reversal occurs (the published predicate of
  `LocalRankOneTitsIndexStatement`; it forces `n ≥ 2`);
- both end vertices are distinguished: every vertex `a` with
  `(e a).val = 0` or `(e a).val + 1 = n` lies in `d.distinguishedVertices`,
  that is, has nonzero restriction to the maximal split torus.

These are the hypotheses of `SpecialLinearTitsCocycleStatement` together with
the outer type and endpoint conditions of `HasRankOneOuterAIndex`, except that
the rank-one conditions (`n = 2 ∨ n = 3`, no other distinguished vertex,
`splitRank G = 1`) are not assumed. It concludes that there exist:

- a field `L : Type u` with `Algebra K L`, `Algebra.IsQuadraticExtension K L`
  and `Algebra.IsSeparable K L`, and a `K`-embedding
  `ι₀ : L →ₐ[K] SeparableClosure K`;
- a matrix `J : Matrix (Fin (n+1)) (Fin (n+1)) L`;
- for every test scheme `T : Over (Spec K)`, a group homomorphism
  `ρ T : (T ⟶ G.X) →* GL_(n+1)(L ⊗_K Γ(T))`, where the coefficient ring is the
  published `SpecialLinear.WeilRoot.tensorAlgebra K L T`;
- characters `χ i` of the actual maximal split torus `d.splitTorus`, for
  `i : Fin (n+1)`;

such that:

1. (Star field.) An absolute Galois element `τ` fixes `ι₀(L)` pointwise if and
   only if `d.star τ` fixes every vertex. Thus `ι₀(L)` is the fixed field of
   the kernel of the star action (the field `TitsIndexData.starField` of
   `OuterTypeAQuadraticExtension`, when that module is available).
2. (Hermitian.) `(J.map c)ᵀ = J`, where `c` is the nontrivial automorphism of
   `L/K` (`(SU3Root.fieldInvolution K L).bar`), and `J.det` is a unit.
3. (Injective.) Every `ρ T` is injective.
4. (Image.) A matrix `g ∈ GL_(n+1)(L ⊗_K Γ(T))` lies in the range of `ρ T` if
   and only if `(g.map c_T)ᵀ * J_T * g = J_T` and `det g = 1`. Here
   `c_T = SU3Root.SchemeModel.coefficientInvolution K L T` is conjugation on
   the `L` factor and `J_T = J.map (algebraMap L (L ⊗_K Γ(T)))`.
5. (Naturality.) For every morphism `a : T' ⟶ T` of test schemes and every
   point `x : T ⟶ G.X`, the matrix of `ρ T' (a ≫ x)` is the matrix of
   `ρ T x` with the published coefficient map
   `SpecialLinear.WeilRoot.tensorMap K L a` applied to every entry.
6. (Split torus.) For every test scheme `T` and point `s : T ⟶ d.splitTorus`,
   the matrix of `ρ T (s ≫ d.splitInclusion)` is the diagonal matrix whose
   `i`-th entry is `1 ⊗ χ i (s)`, where `χ i (s) ∈ Γ(T)ˣ` is read through the
   published `Gm.pointsEquiv` and `1 ⊗ -` is
   `Algebra.TensorProduct.includeRight`.
7. (Restrictions.) For every `i : Fin n`, the actual restriction
   `d.rootRestriction` of the simple root `e.symm i` equals
   `χ i.castSucc - χ i.succ`.

Together, clauses 3 to 5 say that `ρ` is an isomorphism of group functors on
all test schemes from the points of `G` to the determinant-one isometry groups
of `J`; this is the shape consumed by the published
`HermitianRoot.SchemeModel.isoOfMatrixPoints` after a Gram congruence to a
hyperbolic-plus-diagonal model. Nothing is asserted about uniqueness of `L`,
`ι₀`, `J`, `ρ` or `χ`, about the Witt index of `J`, or about the maximal torus
of `d.pinning`.

## Intended use (not part of the statement)

A consumer can apply clause 4 to the diagonal matrices of clause 6 at the
universal point of the split torus. Because these entries are fixed by `c_T`,
it gives `J_ij · χ_i(s) · χ_j(s) = J_ij`, so `J_ij = 0` unless
`χ_i + χ_j = 0`, since the coordinate ring of a split torus is a Laurent
polynomial ring. With clause 7 and the endpoint hypothesis this puts `J` in a
block form adapted to the split torus, from which the Witt-index comparison
with `splitRank G` and the rank-one target are to be derived in separate
statements.

## Provenance (derived statement)

This is a derived, project-internal formulation. The registered source is
J. Tits, *Classification of algebraic semisimple groups*, Proc. Sympos. Pure
Math. 9 (1966), 33–62 (`tits-1966-classification-algebraic-semisimple`).
Section 2.3 (printed p.39 / PDF p.44) defines the index: the actual simple
roots, the zero-restriction set and the star action, formalized by the
Library's `TitsIndexData`. Table II, type `²A_n` (printed p.55 / PDF p.60),
describes the simply connected groups of outer type `A_n` as special unitary
groups `SU_((n+1)/d)(D, h)` of a Hermitian form `h` over a central division
algebra `D` of degree `d` over a quadratic extension `k'`, with an involution
of the second kind, and `h` is a nondegenerate Hermitian form of index `r`.
The same entry lists the distinguished orbits `(d, n+1-d), (2d, n+1-2d), …,
(rd, n+1-rd)` in one-based numbering, so for `r ≥ 1` an end vertex is
distinguished exactly when `d = 1`, `D = k'` and `h` is a Hermitian form on
`k'^(n+1)`. This
statement records that case. It replaces the rational-point description by an
all-test presentation, takes the quadratic extension to be the fixed field of
the star kernel (clause 1), and adds the split-torus clauses 6 and 7, which
hold in a basis adapted to the weights of the maximal split torus. The intended
proof starts from `SpecialLinearTitsCocycleStatement`: normalise the Galois
discrepancies using the split-torus weights and the distinguished end vertex,
obtain a `GL_(n+1)` cocycle, trivialise it by Hilbert 90, read off `J` from the
outer discrepancy, and descend the corrected local isomorphism with the
published `LocalGroupIso.descend`.
