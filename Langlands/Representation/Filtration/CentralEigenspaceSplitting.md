# Splitting a filtration by the scalars of a central element

Authors: Worker 964.

Module `Langlands.Representation.Filtration.CentralEigenspaceSplitting`,
namespace `Langlands.CentralEigenspaceSplitting`. This is an internal helper
module: it proves general linear-algebra facts used for the full cuspidal
Jacquet module of segment representations (Zelevinsky 1980, 3.1 and 9.1(*)).
It states no published proposition and introduces no new mathematical notion
beyond the eigenspace of a central element.

## Setting

Let `k` be a field, `G` a monoid, `A : Rep k G`, and `z : G` central
(`hz : ∀ g, z * g = g * z`). Let `s : ObjectRepFiltration A n` be a finite
filtration `0 = F_0 ≤ F_1 ≤ … ≤ F_n = A`. Assume `z` acts on the `i`-th graded
piece `F_{i+1}/F_i` by a scalar (`hgr : ∀ i v, (s.gradedRepresentation i).ρ z v
= d i • v`).

The intended application is the geometric-lemma filtration of the full
cuspidal Jacquet module of an induced segment representation. A block-scalar
element of the centre of the Levi subgroup acts on its pieces by pairwise
distinct scalars. This central-character argument is the implemented route; it
replaces the bookkeeping of Zelevinsky 1980, §2, which works with
multiplicities of irreducible subquotients. Because each graded piece is acted
on by a scalar, honest eigenspaces suffice and no generalized eigenspaces are
needed.

## Contents

Linear algebra (Lagrange projectors). For an endomorphism `f` killed by the
nodal polynomial `∏ i, (X - c i)` of distinct scalars `c`:

- `aeval_apply_mem`: polynomials in `f` preserve `f`-stable submodules;
- `aeval_basis_mem_eigenspace`: the Lagrange basis polynomial at `c i`,
  evaluated at `f`, maps into the `c i`-eigenspace;
- `sum_aeval_basis`: these projections sum to the identity.

Representations.

- `eigenSubrep ρ z hz a`: the `a`-eigenspace of `ρ z`, as a subrepresentation;
  `mem_eigenSubrep` characterizes membership.
- `eq_iSup_inf_eigenSubrep`: if `ρ z` is killed by the nodal polynomial of
  distinct scalars, every subrepresentation `S` equals `⨆ i, S ⊓ E_i`.
- `range_inf_eigenSubrep_eq_bot`: if a polynomial `p` in `z` kills a
  representation `τ` and `p(a) ≠ 0`, the image of any intertwiner `τ → ρ` meets
  the `a`-eigenspace trivially.
- `isIrreducible_iff_of_equiv`, `exists_ne_zero_of_isIrreducible`,
  `intertwining_aeval`: small general facts (irreducibility is invariant under
  equivalence over any field; an irreducible representation has a nonzero
  vector; intertwiners commute with polynomials in `ρ z`). The first generalizes the
  published complex-coefficient `Langlands.isIrreducible_iff_of_equiv`
  (`Classification/SupercuspidalContragredientAux`) to an arbitrary field, with
  the same proof.

Filtrations with scalar graded actions.

- `gradedProjection_eq_zero_iff`: the graded projection kills exactly the lower
  step.
- `sub_smul_mem_of_graded`: `z - d i` maps `F_{i+1}` into `F_i`.
- `intervalPoly d a b = ∏_{a ≤ i < b} (X - d i)` and `aeval_intervalPoly_mem`:
  it maps `F_b` into `F_a` (induction on `b`).
- `aeval_prod_eq_zero`: `∏ i, (ρ z - d i) = 0` on `A` (the scalars need not be
  distinct).

Distinct scalars (`c` injective, `E_i = eigenSubrep A.ρ z hz (c i)`):

- `aeval_nodal_eq_zero`; `eigenSubrep_le`: `E_i ≤ F_b` when `i < b`;
  `eigenSubrep_inf_eq_bot`: `E_i ⊓ F_b = ⊥` when `b ≤ i`.
- `eigenToGraded`, `eigenToGraded_bijective`, `eigenEquivGraded`: the graded
  projection restricted to `E_i` is an equivalence `E_i ≃ F_{i+1}/F_i`.
  Injectivity is `E_i ⊓ F_i = ⊥`. For surjectivity, a lift `w ∈ F_{i+1}`
  differs from its `E_i`-component by the sum of the other components, which
  lie in `F_i` (components `j < i` because `E_j ≤ F_{j+1}`, components `j > i`
  vanish because they lie in `E_j ⊓ F_{i+1} = ⊥`).
- `iSup_eigenSubrep`: `⨆ i, E_i = ⊤`; `eq_iSup_inf`: `S = ⨆ i, S ⊓ E_i`.

If moreover every graded piece is irreducible (`s.HasSimpleFactors`):

- `isIrreducible_eigenSubrep`, `eigenSubrep_ne_bot`;
- `eigenSubrep_le_or_inf_eq_bot`: each `E_i` lies in `S` or meets it in `⊥`;
- `eq_iSup_eigenSubrep_le`: `S = ⨆ (i) (_ : E_i ≤ S), E_i`, and
  `le_iff_eigenSubrep_le`: `S ≤ S'` iff every `E_i` in `S` is in `S'`;
- `eigenSubrep_le_range_of_eigenvector`: an injective intertwiner from a
  representation with a nonzero `c j`-eigenvector of `z` has image containing
  `E_j`;
- `exists_eigenSubrep_le_range` (detection, subrepresentation form): given an
  injective intertwiner `ι : τ → A` and a nonzero intertwiner `f : τ → σ` with
  `z` acting on `σ` by `a`, some `c j = a` and `E_j ≤ range ι`;
- `eigenSubrep_le_range_iff`: if `B` has a filtration with irreducible pieces
  on which `z` acts by `c (e j)` for an injective `e`, and `ι : B → A` is an
  injective intertwiner, then `E_i ≤ range ι` iff `i` is in the range of `e`.

Without simplicity:

- `exists_eigenSubrep_not_le_ker` (detection, quotient form): given a
  surjective intertwiner `q : A → τ` and a nonzero intertwiner `f : σ → τ` with
  `z` acting on `σ` by `a`, some `c j = a` and `E_j` is not contained in
  `ker q`.

Isolation (the abstract core of both clauses of Zelevinsky 1980, 3.1 and 9.1(*)):

- `not_eigenSubrep_le_ker_of_eigenvector` (distinct scalars only, no
  simplicity): a surjection from `A` onto a representation with a nonzero
  `c i`-eigenvector does not kill `E_i`.

The two isolation theorems assume, in addition to the distinct scalars, that
**every graded piece of the filtration `s` of `A` is irreducible**
(`hs : s.HasSimpleFactors`). They also need the irreducibility of the graded
pieces of each separating representation `B`. Without `hs` they are false: for
`A = k²` with the one-step filtration, trivial actions and `τ = k`, the
conclusions would give `k ≃ k²`.

- `nonempty_equiv_graded_of_sub`. Assume `hs`. Let `ι : τ → A` be injective,
  with a nonzero intertwiner from `τ` to a representation on which `z` acts by
  `c i0`. For every `i ≠ i0`, suppose some surjection `p` from `A` onto a
  representation `B` separates `i` from `i0`. Here `B` has a filtration with
  irreducible pieces on which `z` acts by distinct scalars `c (e j)`, `i` occurs
  among the `e j` and `i0` does not, and `p ∘ ι` is injective or zero. Then `τ`
  is equivalent to the `i0`-th graded piece of `s`. Proof: `p ∘ ι` cannot be
  injective (detection on `B`), so it is zero. Hence `E_i` is not in the range of
  `ι`. `E_i0` is in the range (detection on `A`, using `hs`). Since every
  subrepresentation of `A` is the sum of the `E_i` it contains (again `hs`),
  `range ι = E_i0`, which is equivalent to the `i0`-th piece.
- `nonempty_equiv_graded_of_quot`, the dual statement, also assuming `hs`. Here
  `q : A → τ` is surjective, and a nonzero intertwiner into `τ` comes from a
  representation on which `z` acts by `c i0`. The separating maps are injections
  `ι` from such filtered representations `B`, with `q ∘ ι` surjective or zero.
  Then the `i0`-th graded piece of `s` is equivalent to `τ`. Indeed `q` kills
  every `E_i` with `i ≠ i0`. It does not kill `E_i0`, so by `hs` its kernel meets
  the simple `E_i0` trivially and `q` is injective on `E_i0`.
- `subrepInclusion` (inclusion of a subrepresentation as an intertwiner) and
  `apply_eq_smul_of_equiv` (a scalar action is carried along an equivalence of
  representations).

## Proof notes

All proofs are elementary. The Lagrange projectors come from Mathlib's
`Lagrange.basis` and `Lagrange.nodal`; no finite-dimensionality is assumed, so
the representation may be infinite-dimensional, as Jacquet modules are.
