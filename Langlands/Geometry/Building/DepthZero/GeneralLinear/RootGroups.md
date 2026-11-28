# Root groups of the diagonal torus of `GL_N`

Module `Langlands.Geometry.Building.DepthZero.GeneralLinear.RootGroups`, namespace
`Langlands.Geometry.Building.GeneralLinearParahoric`. Here `F` is a field.

## Declarations

- `diagonalSplitTorus F N` and `diagTorus F N`: the split torus `𝔾_m^N` indexed by
  `ULift (Fin N)` and the diagonal torus `GeneralLinear.diagonalTorus (Fin N)` of `GL_N`.
- `rootCharacter k l`: the character `e_k − e_l` of the diagonal torus;
  `characterLatticeEquiv_rootCharacter`, `rootCharacter_mem_relativeRoots` (for `k ≠ l`) and
  `exists_eq_rootCharacter` (every relative root has this form), from the Library's
  `GeneralLinear.relativeRoots_diagonalTorus`.
- `toMatrixGL`: the rational points of `GL_N` as `GL (Fin N) F`
  (`GeneralLinear.rationalPointsEquiv`), with `toMatrixGL_apply` expressing the entries through
  the global sections.
- `latticePairing_rootCharacter`: the pairing of `e_k − e_l` with the cocharacter of weights
  `m` is `m_k − m_l`.
- `toMatrixGL_apply_of_mem_unipotent` and `toMatrixGL_apply_of_mem_rootGroupPoints`: a point of
  the root subgroup of `a` lies in the dynamic unipotent subgroup of every cocharacter pairing
  positively with `a`, and so has the entries of the identity matrix at the positions `(p, q)`
  where the weight of `p` is at most that of `q`.
- `exists_eq_transvectionGL_of_mem_rootGroupPoints`: **a rational point of the root subgroup of
  `e_k − e_l` is an elementary transvection `1 + t E_{kl}`.**

## Proof

The root subgroup of `a` lies in the dynamic unipotent subgroup `U(λ)` of every cocharacter `λ`
with `⟨a, λ⟩ > 0` (`RelativeRoot.subgroup_le_dynamicUnipotent`). For cocharacters of the split
torus, `λ` composed with the diagonal torus is the Library's diagonal cocharacter with the
lattice weights (`GeneralLinear.cocharacter_comp_eq_diagonalCocharacter_of_diagonal_points`,
using `GeneralLinear.pointsEquiv_diagonalTorus_val`), and its dynamic unipotent subgroup is the
block unipotent subgroup of those weights (`GeneralLinear.unipotent_diagonalCocharacter`,
Conrad–Gabber–Prasad, Example 2.1.1). Applying this to the weights `e_k` (which allows nonzero
off-diagonal entries only in row `k`) and `−e_l` (only in column `l`) leaves the single entry
`(k, l)`.
