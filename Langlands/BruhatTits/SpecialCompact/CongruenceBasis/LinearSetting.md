# Congruence subgroups pulled back along a closed embedding into `GL_N`

This internal unit transfers the matrix results of
`Langlands.BruhatTits.SpecialCompact.CongruenceBasis.GLCongruence` to the
rational points of an affine group scheme `G` over a field `F`. The transfer
goes through a linear representation
`ρ : G ⟶ GeneralLinear.groupScheme (Fin N) F`. The integral structure is
arbitrary: a commutative ring `R`, a ring map `f : R →+* F` and an ideal `I`
of `R`.

## Definitions

- `pointMatrix ρ : rationalPoints G →* GL (Fin N) F` sends a rational point
  to the matrix of its image under `ρ`, using the published
  `rationalPointsEquiv`. `pointMatrix_apply` unfolds it to the
  `pointsEquiv`/`glRingEquiv` description.
- `linearCongruence ρ f I` is the subgroup of rational points `g` such that
  `pointMatrix ρ g` is the image under `f` of an element of `kernel R I`. In
  other words, it is the preimage under `ρ` of the principal congruence
  subgroup of level `I`. `mem_linearCongruence` states this membership.

## Results

Let `χ : 𝔾_m ⟶ G` be a cocharacter whose composite `χ ≫ ρ` is the diagonal
cocharacter of weights `e`. Write `P(χ)`, `Z(χ)`, `U(χ)` and `U(χ⁻¹)` for the
published dynamic parabolic, centralizer, unipotent radical and opposite
unipotent radical.

- `pointMatrix_cocharacter`: the matrix of `χ(t)` is `diag(t ^ e)`. This
  follows from the published `pointsEquiv_diagonalCocharacter` and
  `map_diagonalUnits`.
- `pointMatrix_mem_parabolic` and `pointMatrix_mem_opposite_unipotent` hold
  when `ρ` is a closed immersion. Points of `P(χ)` have block parabolic
  matrices for `e`, and points of `U(χ⁻¹)` have block unipotent matrices for
  `-e`. The proofs use the published `mem_parabolic_iff_of_diagonal` and
  `mem_unipotent_iff_of_diagonal`.
- `pointMatrix_mem_centralizer` and `pointMatrix_mem_unipotent` hold for any
  `ρ`. Points of `Z(χ)` have block Levi matrices, and points of `U(χ)` have
  block unipotent matrices. The proofs use functoriality
  (`centralizer_le_comap`, `unipotent_le_comap`) and the published
  computations `centralizer_diagonalCocharacter` and
  `unipotent_diagonalCocharacter`.
- `exists_linearCongruence_triple`: **Iwahori factorization.** Let `R` be a
  local ring, `I ≤ 𝔪_R` and `ρ` a closed immersion. Then every
  `g ∈ linearCongruence ρ f I` is a product `g = a * b * c` of elements of
  `linearCongruence ρ f I` lying in `U(χ⁻¹)`, `Z(χ)` and `U(χ)`
  respectively. The proof runs as follows.
  1. Choose an integral matrix `C ∈ kernel R I` with image `pointMatrix ρ g`.
     By `isUnit_cellMinor_of_mem_kernel` its cell minor is a unit, so the
     cell minor of the matrix of `g` is a unit too.
  2. The published `exists_mem_parabolic_of_isUnit_cellMinor` (from
     `Dynamic.TriangularCell`) gives `p ∈ P(χ)` with `g * p⁻¹ ∈ U(χ⁻¹)`.
     The separatedness it needs is the published `fieldSeparated`.
  3. Let `b` be the published limit `limit χ p`. Then `b ∈ Z(χ)`
     (`limit_mem_centralizer`) and `p * b⁻¹ ∈ U(χ)`
     (`mul_inv_limit_mem_unipotent`). Conjugation by `b⁻¹ ∈ P(χ)`
     (`conj_mem_unipotent`) gives `b⁻¹ * p ∈ U(χ)`. So
     `g = (g * p⁻¹) * b * (b⁻¹ * p)`.
  4. The matrices of these three factors are an ordered block triple for
     `e`. The integral block factorization `exists_kernel_blockTriple` of `C`
     is another ordered block triple with the same product.
     `blockTriple_eq_map` identifies the factors. So each factor of `g` lies
     in `linearCongruence ρ f I`.
- `conj_mem_linearCongruence`: **contraction.** Let `f` be injective and let
  `t : Fˣ` be the image of an element `r : R`. Then conjugation by `χ(t)`
  preserves the elements of `linearCongruence ρ f I` that lie in `P(χ)`. The
  matrix of `χ(t)` is `diag(t ^ e)`, the matrix of such an element is block
  parabolic, and `diagonalUnits_conj_mem_map_kernel` applies.

The provenance is internal. These are the standard linear-algebra steps
behind Iwahori factorizations of congruence subgroups. No literature
statement is formalized here.
