# Block parabolic and orthogonal coordinates for real Haar measure

Let `B` be a block shape of `n` (`Langlands.GeneralLinear.BlockShape`), with standard parabolic
subgroup `P_B ⊆ GL_n(ℝ)`, Levi factor `M_B` and unipotent radical `U_B`, and let
`K = unitaryCompact ℝ n` be the orthogonal group.

* `leviRadicalOrthogonal B ((m, u), k) = m u k` and `orthogonalRadicalLevi B ((m, u), k) = k u m`
  (with `m` embedded by `B.leviEmbedding ℝ`) are the two multiplication maps.

`RealParabolicHaarStatement`: for every block shape `B`, every Haar measure `μ` on `GL_n(ℝ)` and
Haar measures `μM` on `M_B`, `ν` on `U_B` and `κ` on `K`, there is `c > 0` with

`μ = c • map (leviRadicalOrthogonal B) ((μM × ν) × κ)`,

and, if `μ`, `μM`, `ν` and `κ` are invariant under inversion, also
`μ = c • map (orthogonalRadicalLevi B) ((μM × ν) × κ)` with the same `c`.

`realParabolicHaar` proves it. The Levi–radical factorization of `P_B` is a homeomorphism, and in
these coordinates left multiplication is a skew product (translation in the Levi coordinate and,
in the radical coordinate, translation by a Levi-conjugate), so the pushforward of `μM × ν` is a
Haar measure on `P_B`. The real Iwasawa decomposition `g = npart(g) · torus(alpha g) · kpart(g)`
(`RealIwasawa.npart_mul_torus_mul_kpart`) writes every `g` as an element of the upper triangular
subgroup, hence of `P_B`, times an orthogonal matrix, so the compact factorization theorem
`CompactFactorization.exists_pos_eq_smul_map_mul_prod` gives the constant. Inverting all
coordinates gives the reversed order.

This is the real counterpart of the Library's `ComplexParabolicHaar` (unitary group replaced by
the orthogonal group); it underlies the block Haar coordinates used for the larger-gap recurrence
in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §§9.1 and 10.1.
