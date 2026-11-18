# Eigenvalue bounds from a bounded torus factor and a polynomial additive factor

This helper module bounds the nonnegative eigenvalues of the matrices of real points of a
group over `ℝ` whose closed tori have bounded matrices.

## Declarations

- `RealPolar.abs_mul_mulVec_le`: if every entry of `A` is bounded by `α` in absolute value
  and every entry of `B` by `β`, then
  `|((A * B) *ᵥ v) j| ≤ α * (card n * (β * ∑ k, |v k|))`.
- `RealPolar.le_one_of_pow_le_poly`: if `0 ≤ r`, `0 < a` and `r^N * a ≤ K (N + 1)^D` for all
  `N`, then `r ≤ 1` (an exponential with base `> 1` beats every polynomial; Mathlib's
  `tendsto_pow_const_div_const_pow_of_one_lt`).
- `RealPolar.eigenvalue_le_one` (main result). Let `G` be a group scheme over `ℝ` with
  `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`, and `ρ : MatrixRepresentation G n`.
  Assume `hbound`: for every closed torus `i : T ⟶ G` (`IsTorus T.toGrp`,
  `IsClosedSubgroup i`) there is `α` bounding all entries of `ρ(i(s))` for all real points
  `s` of `T`. If `ρ(x) v = ev • v` for a real point `x`, a nonzero vector `v` and `ev ≥ 0`,
  then `ev ≤ 1`.

## Proof of the main result

The Library's field-general `positivePowerTorusAdditiveFactorization_commute` gives `m > 0`, a
closed torus `i : T ⟶ G`, a point `t` of `T`, and `φ : 𝔾ₐ ⟶ G` with
`x^m = i(t) · φ(1)` and the two factors commuting. Hence `x^{mN} = i(t^N) · φ(1)^N` for every
`N`. The entries of `ρ(i(t^N))` are bounded by `α` (hypothesis), and those of `ρ(φ(1)^N)` by
`c (N + 1)^D` (`RealAdditiveFactor.exists_rationalMatrix_entry_bound`). For a coordinate `j`
with `v j ≠ 0`, `(ev^m)^N |v j| = |(ρ(x)^{mN} v) j|`, which is at most a constant times
`(N + 1)^D` by `abs_mul_mulVec_le`. So `ev^m ≤ 1` by `le_one_of_pow_le_poly`, and `ev ≤ 1`.

## Provenance (internal)

An internal step of the compactness half of `RealAnisotropicCompactConnectedStatement`
(Borel–Tits, *Groupes réductifs* (1965), 9.4, printed p.127, for `k = ℝ`). It mirrors the
non-archimedean argument of the Library's
`MatrixRepresentation.isIntegral_rationalMatrix_of_pow_eq_torus_mul_additive`
(`Langlands.GroupScheme.Rational.CommutingFactorizationIntegrality`), with growth bounds in
place of compactness of the additive factor.
