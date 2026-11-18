# Casselman asymptotics with depth bounded by a fixed-vector dimension

`StablePairingData.IsStablePairing.asymptotics_of_compressedAction_eq_pow_mul`
proves an identity for fixed vectors and fixed smooth functionals. If `C` is
compression by the inverse of the pairing's contracting element, the power
`C ^ d` has image equal to the stable image as soon as `d` bounds the fixed-vector
dimension. The proof uses `pow_apply_eq_zero_of_finrank_le` on the kernel
supremum and `stabilization_of_pow_kill` for the complementary stable image.
When compression by `a` factors as `C ^ d * T`, it therefore sends every fixed
vector into the stable image. The conjugation condition makes `ρ(a)v` fixed
under the upper factor of the pairing data. Averaging then preserves the two
sides of the coefficient identity through `smoothDualPairing_averageMap` and
`IsStablePairing.apply_mk_averageMap`.

`IsStandardCasselmanDepthBound c` records the pairing identity on the dominant
uniformizer lattice for an actual standard parabolic `P_J`. At each basis level
and for each admissible representation with a fixed-vector dimension bound `d`,
it requires depth at least `d * c` on the simple roots outside `J`.
`exists_standardCasselman_boundedDepth` proves the existence of such a `c`
for a basis shared by the faces `J` and `∅`. The chosen strict
point of its split component is a uniformizer power `ϖ^z`, where `z` is
nonnegative on all simple roots and zero on `J`. Let `c` be the largest absolute
value of its simple-root pairings, with value zero for an empty root set. If the
pairings of a dominant `y` outside `J` are at least `d * c`, then `y - d • z` is
still dominant. The minimal standard parabolic's factorization gives
multiplicativity of compression for `(ϖ^z)^d * ϖ^(y - d • z)` on the common
basis level. The first factor compresses as `C ^ d` by
`compressedAction_inv_pow_apply`. The inclusions of the opposite radical of
`P_J` in the minimal opposite radical supply the conjugation condition.

This is a fixed-level refinement of the Casselman identity in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
Proposition I.4.3 (printed pp. 245–246). The dimension bound is derived from the
Library's compression lemmas for use with the orbit-uniform depth in VI.2.3.
