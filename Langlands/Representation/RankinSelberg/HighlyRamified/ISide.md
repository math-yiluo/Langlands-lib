# The forward side of Jacquet–Shalika §4.4

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`; it proves the
equality `I₁ = I₂` of Jacquet–Shalika 1985, §4.4 (printed pages 330–331), pointwise.

`IsDeepFirstRow f z` says that `z ∈ F^(n+1)` has `z_last ≠ 0`, `z_last⁻¹ ∈ 𝔭^f` and
`z_j / z_last ∈ 𝔭^f` for the other coordinates. In the source `z = (u, x, y)` with
`y = z_last`; the conditions are those checked at the end of the proof (printed page 331).

`eq_at_weyl_firstRow`: let `W₁, W₂` be functions on `GL_(n+2)(F)` that are right invariant
under the published level subgroup `Conductor.levelSubgroup F (n+1) f`, satisfy
`W_i(z g) = ω(z) W_i(g)` for scalars `z`, and agree on the mirabolic subgroup. For every
`g ∈ GL_(n+1)(F)` and deep first row `z`, `W₁(diag(g,1) w n(z)) = W₂(diag(g,1) w n(z))`.
The last row of `diag(g,1) w n(z)` is `(1, z_0, …, z_n)` (published
`lastRow_rankInclusion_one_mul` and `weylLong_mul_firstRowUnipotent_last`), so
`eq_of_lastRow_congruence` applies.

`testValue_eq_at_weyl` sums this over a finite weight `Φ` supported on deep first rows:
`Σ_z Φ(z) W₁(diag(g,1) w n(z)) = Σ_z Φ(z) W₂(diag(g,1) w n(z))`. These are the values at
`diag(g,1)` of the right translates by `w` of the test vectors, so the two forward
corank-one integrals coincide.
