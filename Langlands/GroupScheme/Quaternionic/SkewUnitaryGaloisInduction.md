# The inductive step of the special unitary Hasse principle

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisInduction`.

Over a number field `F`, for a central quaternion division algebra `D` with an involution
`σ` of the first kind with `dim D^σ = 3` (`hdim`, `hsym`) and `τ = σ.quaternionConjugation`:

- `SUHasse σ hdim hsym n` is the proposition: for every invertible `τ`-antihermitian `n × n`
  Gram matrix `H` over `D`, every finite Galois `L/F` and every crossed homomorphism
  `c : Gal(L/F) → suGroup τ H L` with `IsLocallyCoboundary τ H c`, there is
  `a ∈ suGroup τ H L` with `c s = a * s(a)⁻¹`. It is the injectivity of
  `H¹(L/F, SU(h)) → ∏_v H¹(F_v, SU(h))` on the kernel, in Galois terms (Kneser, *Lectures on Galois Cohomology of Classical Groups* (TIFR Lectures on Mathematics 47, 1969), §5.11,
  p. 101).
- `vecMap`, `matrixSesqBilin_vecMul`, `matrixSesqBilin_gramOver`, `GramDescent.inv_gram_eq`
  and related lemmas compute values of forms on transformed rows.
- `suHasse_adjoin`: given proper Witt transitivity in rank `m + 1` over every field of
  characteristic zero containing `F` and `SUHasse` in rank `m`, the conclusion holds for
  `H = adjoinSkewLine H₁ c₀` (`H₁` invertible antihermitian, `c₀ ≠ 0` alternating).

Proof of `suHasse_adjoin` (the argument of Kneser, *Lectures on Galois Cohomology of Classical Groups* (TIFR Lectures on Mathematics 47, 1969), §5.11, following the case of quadratic
forms): by Hilbert 90, `c s = p * s(p)⁻¹` and the twisted Gram matrix `H'` descends to `D`
(`exists_gramDescent`). Local coboundary data show that `H'` represents `c₀` at every place
(`GramDescent.isLocallyRepresented`), hence globally
(`numberFieldSkewRepresentation`, rank at least two) by a row `y` over `D`. The row
`z = y p⁻¹` over `L` has value `c₀` for `H`; proper Witt transitivity over `L` gives
`w ∈ suGroup τ H L` sending the last row to `z`. The twisted crossed homomorphism
`w * c s * s(w)⁻¹` fixes the last row, hence is a block crossed homomorphism `c₁` for `H₁`
(`exists_block_cocycle`); it is locally a coboundary (`IsCoboundaryAt.block`, using proper
Witt transitivity over the completions), so the induction hypothesis and
`exists_coboundary_of_block` give the primitive.
