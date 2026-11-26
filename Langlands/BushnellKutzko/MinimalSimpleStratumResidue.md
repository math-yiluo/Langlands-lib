# Residues of integral units of a normalizing field

The module `Langlands.BushnellKutzko.MinimalSimpleStratumResidue` relates the reduced
characteristic polynomial of an integral unit of a normalizing field to the minimal polynomial of
its residue, and the action of such residues on the successive quotients of a lattice chain.

Throughout, `F` is a nonarchimedean local field, `𝓛 = (L_i)` an `𝒪_F`-lattice chain in `V`, and
`E` a field acting on `V` (`Module E V`, `IsScalarTower F E V`) whose units lie in
`𝓛.stabilizer`. The ring `𝔬_E = subfieldIntegers F E` is assumed to be a discrete valuation ring
with `algebraMap 𝒪_F 𝔬_E` a local homomorphism; Mathlib then supplies the algebra
`k_F = ResidueField 𝒪_F → k_E = ResidueField 𝔬_E`.

## Declarations

- `residueJacobsonEquiv O : ResidueField O ≃+* O ⧸ Ring.jacobson O` for a local ring `O`, the
  identification through `IsLocalRing.ringJacobson_eq_maximalIdeal`; the Library writes the
  coefficient ring of `Stratum.fundamentalPolynomial` as `𝒪_F ⧸ Ring.jacobson 𝒪_F`.
  `residueJacobsonEquiv_residue` and `map_residue_map_residueJacobsonEquiv` compute it on classes
  and on reduced polynomials.
- `LatticeChain.reduceIntegralPolynomial_charpoly_eq_minpoly_pow`: for a unit `w` of `𝔬_E` with
  residue `c ∈ k_E`, the element `c` is integral over `k_F`, and for some `m > 0`

  ```text
  reduceIntegralPolynomial 𝒪_F F (charpoly of w acting on V) = (minpoly k_F c mapped to 𝒪_F/Jac(𝒪_F))^m.
  ```
- `LatticeChain.subfieldLayer_isScalarTower_residue`: on each layer `L_i/L_{i+1}`, with the action
  of `k_E` given by `LatticeChain.subfieldLayerResidueModule`, the action of `k_F` through `k_E` is
  its own residue action.
- `LatticeChain.exists_layerEquiv_residue_intertwine`: for two such fields `E₁`, `E₂` and residues
  `c₁ ∈ k_{E₁}`, `c₂ ∈ k_{E₂}` with `c₁` integral over `k_F` and the same minimal polynomial over
  `k_F`, every layer `L_r/L_{r+1}` has an `𝒪_F`-linear automorphism `ψ` with
  `ψ (c₂ • q) = c₁ • ψ q`.

## Proofs

For the characteristic polynomial, take a monic lift `P ∈ 𝒪_F[X]` of the minimal polynomial of
`c` over `k_F` (`Polynomial.lifts_and_degree_eq_and_monic`). Its value `P(w)` has residue zero, so
it is a multiple of a uniformizer of `𝔬_E`; since a uniformizer of `E` shifts the chain by a
positive amount (`fieldShift_uniformizer_pos`) and `𝔬_E` preserves every lattice
(`subfieldInteger_smul_mem`), `P(w)` maps each `L_i` into `L_{i+1}` and `P(w)^e` maps `L_0` into
`ϖ L_0`. `LatticeChain.reduceIntegralPolynomial_charpoly_eq_pow` of
`Langlands.BushnellKutzko.PureStratumTopNonsplitProof` then gives the power of the reduction of
`P`, which is the transported minimal polynomial. The argument is the one of
`LatticeChain.exists_reduceIntegralPolynomial_charpoly_eq_pow` in that module, with the residue
algebra of Mathlib so that the irreducible factor is named.

For the layers, `L_r/L_{r+1}` is a finite-dimensional `k_F`-vector space, since `L_r` is finitely
generated over `𝒪_F`. Multiplication by `c_j` is a `k_F`-linear endomorphism
(`Algebra.lsmul`) killed by the common minimal polynomial, which is irreducible.
`exists_linearEquiv_conj_of_aeval_irreducible` gives a `k_F`-linear automorphism carrying
multiplication by `c₂` to multiplication by `c₁`; restricting scalars gives `ψ`.

## Sources

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), the polynomial
`φ_b` on printed p. 58 (PDF p. 70) and (2.5.8), printed p. 80 (PDF p. 92); source
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994), (1.4), printed
pp. 112–113 (PDF pp. 125–126); source `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
SHA-256 `fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
