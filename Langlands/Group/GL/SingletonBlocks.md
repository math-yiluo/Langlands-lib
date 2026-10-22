# The singleton block shape and the upper unipotent group

Author: Worker 204.

This module specializes the Library's standard block geometry
(`Langlands.Group.GL.Blocks`, `Langlands.Group.GL.BlockModulus`) to the
ordered shape with `n` blocks of size one, the Borel case. It proves that the
block parabolic is then the upper triangular group, that its unipotent radical
is the Library's actual upper unipotent group `upperUnipotent n R` from
`Langlands.Group.GL.UpperUnipotent`, that Levi elements are diagonal matrices
acting by conjugation, and that the block modulus is the usual product of root
quotients. Results stated for an arbitrary `BlockShape` (radicals, Levi
actions, block moduli) therefore specialize to `upperUnipotent n R`.

Every statement below holds for every natural number `n`, including `n = 0`
(where all groups are trivial and products are empty). The ring statements
hold for every commutative ring `R : Type u`. No existing definition is
changed or redefined; no new topology is installed. No hypothesis assumes any
of the identifications proved here.

## Provenance

Internal. The module introduces one block shape and one homomorphism, both
determined by the task contract (task 15b0c237, revision 2), and otherwise
proves identifications between existing Library definitions. The mathematical
content is the standard description of the Borel subgroup of `GL_n`: with all
blocks of size one, the block upper triangular condition is the upper
triangular condition, the diagonal block condition of the radical is
"diagonal entries equal to one", the Levi is the diagonal torus, and the
modulus `∏_(i<j) |det m_i|^(n_j) / |det m_j|^(n_i)` of
`Langlands.PadicField.TopologicalData.leviModulus` becomes
`∏_(i<j) |t_i| / |t_j|` because all `n_i = 1` and `det` of a `1 × 1` scalar
matrix is its entry. Each claim is a direct computation from the Library
definitions cited by name below.

## Definitions

- `Langlands.GeneralLinear.BlockShape.singletons (n : ℕ) : BlockShape n`:
  `length = n`, every `size i = 1`; positivity is `Nat.one_pos` and the size
  sum is `∑ i : Fin n, 1 = n`. It is an `abbrev` (reducible), so that type
  class instances and lemmas for `Fin n` and `Fin 1` apply to its block index
  type `Fin (singletons n).length` and to each coordinate type
  `Fin ((singletons n).size i)`. The instances `singletons_size_neZero` and the
  `Unique (Fin ((singletons n).size i))` instance record that each block has
  exactly one coordinate.
- `Langlands.GeneralLinear.BlockShape.upperUnipotentEquivRadical R :
  upperUnipotent n R ≃* (singletons n).unipotentRadical R`: sends `u` to the
  parabolic element with the same invertible matrix, which lies in the radical
  by `singletons_mem_unipotentRadical_iff`; the inverse forgets the parabolic
  layer. Both directions leave the underlying invertible matrix unchanged, and
  the inverse laws and multiplicativity hold definitionally.
- `Langlands.GeneralLinear.BlockShape.upperUnipotentContinuousEquivRadical R`
  (under `[TopologicalSpace R]`): the same equivalence bundled as
  `upperUnipotent n R ≃ₜ* (singletons n).unipotentRadical R`, for the existing
  subspace topologies of both subgroups inside `GeneralLinear n R`. Both
  directions are continuous because they are built from subtype inclusions and
  `Continuous.subtype_mk`.
- `Langlands.GeneralLinear.BlockShape.singletonLevi R :
  (Fin n → Rˣ) →* (singletons n).Levi R`: sends `t` to the family of `1 × 1`
  scalar matrices `GeneralLinear.scalar (t i)`. It is a monoid homomorphism
  because `GeneralLinear.scalar` is.

## Theorems

Index identification (contract item 1):

- `singletons_length : (singletons n).length = n` and
  `singletons_size i : (singletons n).size i = 1` (both `rfl`).
- `singletons_indexEquiv_apply (i : Fin n) (j : Fin 1) :
  (singletons n).indexEquiv ⟨i, j⟩ = i` (simp). This holds only
  propositionally: `indexEquiv` is `finSigmaFinEquiv.trans (finCongr _)`, and
  the proof unfolds it with Mathlib's `finSigmaFinEquiv_apply`, reducing the
  value to `∑ k < i, 1 + j = i` with `j = 0`.
- `singletons_index (i : Fin n) (j : Fin 1) : (singletons n).index i j = i`
  (simp), the same statement for the coordinate embedding `index`.

Membership (contract item 2):

- `singletons_mem_parabolic_iff R g :
  g ∈ (singletons n).parabolic R ↔ g.val.IsUpperTriangular`, for every
  `g : GeneralLinear n R`. Proof: `mem_parabolic_iff` and
  `singletons_index`.
- `singletons_unipotentSubgroup R :
  (singletons n).unipotentSubgroup R = upperUnipotent n R`. Proof:
  `mem_unipotentSubgroup_iff`, the previous lemma, and the diagonal block
  condition `g (index i a) (index i b) = if a = b then 1 else 0`, which for
  one-coordinate blocks says `g i i = 1`.
- `singletons_mem_unipotentRadical_iff R g :
  g ∈ (singletons n).unipotentRadical R ↔ g.val ∈ upperUnipotent n R`, for
  `g : (singletons n).parabolic R`, using that `unipotentSubgroup` is the
  image of `unipotentRadical` under the injective subgroup inclusion.

Identification (contract item 3):

- `upperUnipotentEquivRadical_apply_val R u` (simp): the `GeneralLinear n R`
  element underlying `upperUnipotentEquivRadical R u` is `u` itself.
- `upperUnipotentEquivRadical_symm_apply_val R v` (simp): the element
  underlying the inverse image of `v` is the element underlying `v`.
- `upperUnipotentContinuousEquivRadical_toMulEquiv R` and
  `upperUnipotentContinuousEquivRadical_apply R u` (simp): the continuous
  version has the multiplicative equivalence above as its underlying map.

Diagonal Levi elements (contract item 4):

- `singletonLevi_apply R t i` (simp): `singletonLevi R t i =
  GeneralLinear.scalar (t i)`.
- `leviEmbedding_singletonLevi_val R t :
  ((singletons n).leviEmbedding R (singletonLevi R t)).val =
  Matrix.diagonal fun i => (t i : R)`. Proof: entrywise, using the Library's
  `leviEmbedding_apply_same` and `leviEmbedding_apply_ne` together with
  `singletons_index`.

Levi action in matrix terms (contract item 5):

- `leviAction_apply_val R B m v` (simp), for every block shape
  `B : BlockShape n`, every `m : B.Levi R` and every
  `v : B.unipotentRadical R`: the `GeneralLinear n R` element underlying
  `B.leviAction R m v` is
  `B.leviEmbedding R m * v * (B.leviEmbedding R m)⁻¹`. This holds by
  definition of `leviAction` (conjugation by `leviInParabolic`).
- `leviAction_singletonLevi_upperUnipotentEquivRadical R t u`: for
  `L = (singletons n).leviEmbedding R (singletonLevi R t)`, the element
  underlying `(singletons n).leviAction R (singletonLevi R t)
  (upperUnipotentEquivRadical R u)` is `L * u * L⁻¹`.

Modulus (first formula of contract item 7), in namespace
`Langlands.PadicField.TopologicalData`:

- `leviModulus_singletonLevi T t`: for every prime `p` with
  `[Fact p.Prime]`, every `F : PadicField.{u} p` in an arbitrary carrier
  universe, every `T : F.TopologicalData` and every `t : Fin n → F.Carrierˣ`,
  `T.leviModulus (singletons n) (singletonLevi F.Carrier t) =
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j),
  T.normalizedAbsUnits (t i) / T.normalizedAbsUnits (t j)` in `ℝ≥0ˣ`.
  Proof: `leviModulus_apply`, then `determinantNorm_scalar` with exponent one
  in each factor.

## Role

The Rankin–Selberg module
`Langlands.Representation.RankinSelberg.CharacterChangeSingletonBlocks`
uses these identifications to realize the character-change diagonal as a
singleton Levi element. Downstream, the unipotent character-change modulus
statement can then be obtained from the general block results by transport
along `upperUnipotentContinuousEquivRadical`.
