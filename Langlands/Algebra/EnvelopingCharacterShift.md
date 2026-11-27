# Shifting an enveloping algebra by a linear form vanishing on brackets

Module `Langlands.Algebra.EnvelopingCharacterShift`. It works with a complex Lie algebra `L`, its
universal enveloping algebra `U(L)` (Mathlib's `UniversalEnvelopingAlgebra ℂ L`), and a
complex linear form `μ : L → ℂ`.

## The shift automorphism

If `μ ⁅U, V⁆ = 0` for all `U, V`, then `U ↦ U + μ(U)·1` is a Lie algebra homomorphism
`L → U(L)` (`shiftLie`). The two summands commute and the scalar part of a commutator
vanishes. Its extension to `U(L)` is the algebra endomorphism `shift μ hμ` with
`shift μ hμ (ι U) = ι U + μ(U)` (`shift_ι`). The shifts by `μ` and by `-μ` compose to the
identity (`shift_comp_neg`, proved by `UniversalEnvelopingAlgebra.hom_ext` on generators), so
`shift μ hμ` is surjective (`shift_surjective`). A surjective algebra endomorphism maps central
elements to central elements (`shift_mem_center`), which gives the algebra endomorphism
`centerShift μ hμ` of the center `Subalgebra.center ℂ U(L)` (`centerShift_val`).

## Intertwining

Let `ρ : L → A` be a Lie homomorphism into an associative complex algebra (with the commutator
bracket) and `T ∈ A` with

`ρ(U) T = T (ρ(U) + μ(U))` for every `U ∈ L`.

- `lift_mul_eq_mul_lift_shift`: if `μ` vanishes on brackets, then `ρ̃(y) T = T ρ̃(shift μ y)`
  for every `y ∈ U(L)`, where `ρ̃ = UniversalEnvelopingAlgebra.lift ℂ ρ`. The proof is by
  induction on a preimage of `y` in the tensor algebra. Scalars commute with `T`, generators
  are the hypothesis, and products and sums follow from multiplicativity and additivity.
- `lie_eq_zero_of_intertwining`: if `T ≠ 0` and `A` has no zero divisors as a complex vector
  space (`NoZeroSMulDivisors ℂ A`), the hypothesis alone forces `μ ⁅U, V⁆ = 0`. Indeed
  `ρ⁅U, V⁆ = ρ(U)ρ(V) − ρ(V)ρ(U)`, and moving `T` to the left through both products gives
  `ρ⁅U, V⁆ T = T ρ⁅U, V⁆`. The hypothesis for `⁅U, V⁆` gives `ρ⁅U, V⁆ T = T (ρ⁅U, V⁆ + μ⁅U, V⁆)`.
  Comparing the two gives `μ⁅U, V⁆ • T = 0`, hence `μ⁅U, V⁆ = 0`.
- `exists_centerShift_intertwining` combines the two: under these hypotheses there is an algebra
  endomorphism `θ` of the center of `U(L)` with `ρ̃(z) T = T ρ̃(θ z)` for every central `z`.

## Provenance

Internal. The construction is the universal property of the enveloping algebra
(`UniversalEnvelopingAlgebra.lift`) applied to `U ↦ U + μ(U)`. Its intended use is the
following. If `T` is multiplication by a smooth character `χ` of a Lie group and `μ` is the
derivative of `χ` at the identity, the Leibniz rule gives `X(χu) = χ(Xu + dχ(X)u)`, which is the
hypothesis above. The lemmas then show that multiplication by `χ` changes the action of the
enveloping algebra, and of its center, by the shift. On the infinite adelic points of a group
scheme this is `Langlands.Global.InfiniteAdelicGroupPoints.exists_centerShift_plotSmoothMultiplication`.
Combined with a finite transfer of centers to a Levi subgroup (as in Mœglin–Waldspurger,
*Spectral decomposition and Eisenstein series* (1995), I.2.17), it shows that twisting by a
character of the Levi preserves center finiteness
(`Langlands.Global.parameterTwistCenterFiniteReduction`). The Library's
`Langlands.Global.ArchimedeanGL.envelopingShift` is the same construction for the archimedean
`GL_n`. This module states it for an arbitrary complex Lie algebra.
