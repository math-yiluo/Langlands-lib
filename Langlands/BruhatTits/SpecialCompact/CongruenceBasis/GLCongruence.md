# Principal congruence subgroups of `GL_N` and their block factorizations

This internal unit is the matrix layer of the congruence-tower construction in
`Langlands.BruhatTits.SpecialCompact.CongruenceBasis.Assembly`. Everything is
stated for matrices indexed by `Fin N` and for an integer weight vector
`e : Fin N → ℤ`. The block subgroups `blockParabolicSubgroup`,
`blockLeviSubgroup` and `blockUnipotentSubgroup`, the Levi projection
`blockLeviProjection`, the cell minor `cellMinor` and the diagonal points
`diagonalUnits` come from the published modules
`Langlands.GroupScheme.Dynamic.GeneralLinearCell` and
`Langlands.GroupScheme.Dynamic.GeneralLinearOrbit`.

## Definitions

- `kernel R I` is the principal congruence subgroup of level `I` in
  `GL_N(R)`, for a commutative ring `R` and an ideal `I`. It is the kernel of
  the reduction map `GL_N(R) → GL_N(R/I)`.
- `conjMatrix e t C` is an auxiliary integral matrix. Its `(i, j)` entry is
  `t ^ (e i - e j) * C i j` when `e j ≤ e i`, and `0` otherwise. For a block
  parabolic `C`, its image is `diag(t ^ e) C diag(t ^ e)⁻¹`.

## Results

- `mem_kernel_iff`: `C ∈ kernel R I` exactly when every entry of `C - 1`
  lies in `I`. `ringHom_one_apply` is the entrywise form of `f 1 = 1` that
  this proof uses.
- `blockLeviSubgroup_le_blockParabolicSubgroup` and
  `blockUnipotentSubgroup_le_blockParabolicSubgroup` are the two inclusions
  into the block parabolic subgroup.
  `disjoint_blockLeviSubgroup_blockUnipotentSubgroup` follows by comparing
  entries. `disjoint_blockUnipotentSubgroup_neg_blockParabolicSubgroup` is the
  published `blockUnipotentSubgroup_neg_inf_blockParabolicSubgroup`.
- `blockTriple_injective`: the ordered product map
  `U(-e) × L(e) × U(e) → GL_N(A)` is injective. The proof applies
  `Subgroup.mul_injective_of_disjoint` twice, first to `U(-e)` and the block
  parabolic subgroup, then to `L(e)` and `U(e)`.
  `eq_one_of_blockTriple_eq_one` is its special case at the identity.
  `blockTriple_eq_map` says that if an ordered triple over `B` multiplies to
  the image under `f : A →+* B` of an ordered triple over `A`, then the
  factors are the images. It applies injectivity over `B`, using the
  published lemmas that ring maps preserve the block subgroups.
- `blockDiagonalPart_blockDiagonalPart`, `blockLeviProjection_mem` and
  `inv_blockLeviProjection_mul_mem` give the Levi part of a block parabolic
  matrix `p` and show that `(Levi part)⁻¹ * p` is block unipotent. The last
  proof uses the published `blockUnipotent_iff` and
  `blockDiagonalPart_mul`.
- `cellMinor_one`: the cell minor of the identity matrix is `1`.
- `isUnit_cellMinor_of_mem_kernel`: let `R` be local and `I ≤ 𝔪_R`. If
  `C ∈ kernel R I`, then `cellMinor e C` is a unit. Reduction modulo `I`
  commutes with cell minors (`map_cellMinor`), so the minor is congruent to
  `1` modulo `I`, hence modulo `𝔪_R`, and therefore it is not in the maximal
  ideal.
- `exists_kernel_blockTriple`: **block factorization of congruence
  matrices.** Under the same hypotheses, every `C ∈ kernel R I` can be written
  as `C = u * d * v` with `u ∈ kernel R I ⊓ U(-e)`,
  `d ∈ kernel R I ⊓ L(e)` and `v ∈ kernel R I ⊓ U(e)`. The published
  `exists_cell_decomposition` applies because the cell minor is a unit. It
  gives `C = u * p` with `u ∈ U(-e)` and `p` block parabolic. Then `d` is the
  Levi projection of `p` and `v = d⁻¹ * p`. Reducing modulo `I` gives an
  ordered block triple equal to `1`, so by `eq_one_of_blockTriple_eq_one`
  every factor reduces to `1`.
- `map_conjMatrix` and `diagonalUnits_conj_mem_map_kernel`:
  **diagonal conjugation.** Let `f : R →+* K` be injective, with `K` a field,
  and let the unit `u : Kˣ` be the image `f t` of `t : R`. If
  `C ∈ kernel R I` has block parabolic image in `GL_N(K)`, then
  `diag(u ^ e) f(C) diag(u ^ e)⁻¹` is again the image of an element of
  `kernel R I`. The candidate is `conjMatrix e t C`, and the proof checks the
  following.
  1. Its image is the conjugate, entry by entry, using the published
     `diagonalUnits_conj_apply`. The entries with `e i < e j` vanish because
     the image is block parabolic.
  2. It is invertible with inverse `conjMatrix e t C⁻¹`. This holds after
     applying the injective `f`.
  3. It is congruent to `1` modulo `I` entry by entry. The diagonal entries
     equal those of `C`. The off-diagonal entries are multiples of those of
     `C` or zero.

The level ideal `I` and the ring `R` are arbitrary here. No property of local
fields is used. The provenance is internal: these are the standard
elementary facts about principal congruence subgroups, proved from the
published block-matrix library. No literature statement is formalized here.
