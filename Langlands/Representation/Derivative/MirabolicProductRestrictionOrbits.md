# The two mirabolic orbits on the binary-parabolic flag variety

Author: Worker 1163.

This helper module of the proof of
`Langlands.Derivative.MirabolicProductRestrictionStatement` describes the right
action of the mirabolic subgroup on `P \ GL_N`, where `N = (m+1)+(n+1)` and `P`
is the upper block parabolic of the binary shape `(m+1, n+1)`, and packages the
two orbits as an ordered double-coset enumeration in the sense of the published
`Langlands.Geometric.OrderedDoubleCosets`. This is the orbit description used
in Bernstein–Zelevinsky (1977), §7.1, printed p.471 (one-based PDF page 32):
two orbits, the closed orbit of `P e` and the open orbit of `P w⁻¹` for a
permutation matrix `w`. The Lean representative `w` is an explicit coordinate
permutation chosen to match the published case (III) coordinates; the source's
cyclic permutation is not used.

## Setting

Everything is over an arbitrary field `K`; the topological part assumes
`[TopologicalSpace K] [IsTopologicalRing K] [T1Space K]`.

- `shape m n` is the published `BlockShape.binary (m+1) (n+1)`.
- `parabolicP K m n` is its published upper block parabolic in
  `GL_((m+1)+(n+1))(K)`, and `mem_parabolicP_iff` says that membership means
  vanishing of the lower-left block (rows `natAdd`, columns `castAdd`).
- `mirabolicQ K m n` is the published `mirabolic ((m+1)+n) K`, viewed as a
  subgroup of the same group (`GL_((m+1)+(n+1))` is definitionally
  `GL_(((m+1)+n)+1)`).

## The invariant

`lastInvRow m n g` is the last row of `g⁻¹`, and `IsClosedCell m n g` says that
it vanishes on the first block. The proof that this invariant separates the two
orbits is elementary linear algebra:

- `isClosedCell_mul`: if `p ∈ P` and `q ∈ Q` then `p q` is a closed cell, since
  the last row of `q⁻¹ p⁻¹` is the last row of `p⁻¹`, which lies in the second
  block.
- `openIndex` is the permutation `Fin N ≃ Sum (Fin (m+1)) (Fin (n+1)) ≃ Fin N`
  through the published case (III) coordinate map `rightIndex (n+1) m`; `openRep`
  is its permutation matrix `w` (published `GeneralLinear.permutation`). The
  last row of `w` is the unit vector at the last coordinate of the first block
  (`openRep_lastRow`), and `w⁻¹ g w` has entries `g (openIndex x) (openIndex y)`
  (`openRep_conj_apply`, from the published `permutation_conjugate_entry`).
- `not_isClosedCell_mul`: for `p ∈ P`, `q ∈ Q`, the last row of
  `(p w⁻¹ q)⁻¹` is row `castAdd (last m)` of `p⁻¹`, whose first-block part is the
  last row of the invertible Levi block of `p⁻¹`, hence nonzero
  (`exists_row_ne_zero`).
- `exists_eq_mul_of_isClosedCell`: if `g` is a closed cell, choose `b ∈ GL_(n+1)`
  whose last row is the second-block part of `lastInvRow g` (nonzero), and put
  `p₀ = blockUpper 1 b 0`; then `p₀ g ∈ Q` and `g = p₀⁻¹ (p₀ g)`.
- `exists_eq_mul_openRep_of_not_isClosedCell`: otherwise choose `a ∈ GL_(m+1)`
  whose last row is the first-block part, let `x` have the second-block part as
  its last row, and put `p₀ = blockUpper a 1 x`; then `w p₀ g ∈ Q` and
  `g = p₀⁻¹ w⁻¹ (w p₀ g)`.

`blockUpper h₀ h₁ x` is the invertible block matrix `[h₀ x; 0 h₁]`, built from the
published `TwoBlock.matrix` by `reindex finSumFinEquiv`, with its four block
entry lemmas and `blockUpper_mem`. The published
`Langlands.Derivative.Mirabolic.exists_lastRow_eq_of_ne_zero` supplies the fact that
every nonzero row is the last row of an invertible matrix; see
[MinusVanishing](MinusVanishing.md).

## Orbits and ordering

- `mem_cosetOrbit_iff`: for any group, `P g` lies in the published
  `Geometric.cosetOrbit P Q w` iff `g = p w⁻¹ q` with `p ∈ P`, `q ∈ Q`.
- `mem_closedOrbit_iff` and `mem_openOrbit_iff`: `P g` is in the orbit of `1`
  iff `g` is a closed cell, and in the orbit of `w` iff it is not.
- `isOpen_openOrbit`: the open orbit is open in the quotient topology, because
  its preimage is the finite union of the sets where an entry of the last row of
  `g⁻¹` is nonzero; inversion is continuous on the unit group and `K` is `T1`.
- `orbitOrdering m n : OrderedDoubleCosets (parabolicP K m n) (mirabolicQ K m n) 2`
  has representatives `![openRep K m n, 1]`: the orbits cover, are disjoint, and
  the initial unions (empty, the open orbit, everything) are open.

## Imports

`Geometric.ClosedSubgroupDefinitions` (for `cosetOrbit` and
`OrderedDoubleCosets`), `Group.GL.Maps` (permutation matrices),
`Group.GL.MirabolicMixedProductSubgroups` (`TwoBlock.matrix`, `rightIndex`) and
`Group.GL.MirabolicOppositeIntersection` (`BlockShape.binary` and its index
lemmas). Only definitions and elementary published lemmas about them are used.
