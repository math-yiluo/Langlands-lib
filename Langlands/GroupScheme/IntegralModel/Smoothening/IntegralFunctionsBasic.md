# Points and divisibility of integral functions

Module `Langlands.GroupScheme.IntegralModel.Smoothening.IntegralFunctionsBasic`.
This is a helper module of the proof of
`Langlands.GroupScheme.IntegralModel.SmootheningStatement`. It contains internal
lemmas about `integralFunctions R K A`, which is defined in
`Langlands.GroupScheme.IntegralModel.IntegralFunctions`.

Let `R` be a commutative ring with fraction field `K` (`IsFractionRing R K`), and
let `A` be a commutative `R`-algebra. Write `B = integralFunctions R K A`. This
is the ring of elements of `K ⊗[R] A` whose value `genericEval R K A φ` at every
`R`-point `φ : A →ₐ[R] R` lies in `R`. Bruhat–Tits II, §1.7.3 f)
(`bruhat-tits-1984-reductive-local-groups-ii`) uses this ring.

- `one_tmul_mem_integralFunctions`: `1 ⊗ a ∈ B` for `a ∈ A`, because
  `genericEval R K A φ (1 ⊗ a) = φ a`. It needs no fraction-field hypothesis.
- `incl R K A : A →ₐ[R] B`, `a ↦ 1 ⊗ a` (`coe_incl`). If `A` is flat, `incl` is
  injective (`incl_injective`).
- Instances `isTorsionFree_tensor` and `isTorsionFree_integralFunctions`: when `R`
  is a domain, `K ⊗[R] A` and `B` are torsion-free `R`-modules (via
  `smul_left_cancel` of the Saturation module).
- `point φ : B →ₐ[R] R` is the value at the `R`-point `φ`. It is the map
  `genericEval R K A φ` restricted to `B`, which lands in `⊥ ≅ R`
  (`Algebra.botEquivOfInjective`). `algebraMap_point` relates it to
  `genericEval`. `point_incl` and `point_comp_incl` say that `point φ` extends
  `φ`, and `point_smul` that `point φ (s • b) = s * point φ b`.
- `eq_point`: when `R` is a domain, every `R`-algebra map `ψ : B → R` equals
  `point (ψ ∘ incl)`. This uses the uniqueness lemma `algHom_ext` with target
  `R`. So restriction along `incl` is a bijection from the `R`-points of `B` to
  those of `A`.
- `exists_eq_smul_of_dvd`: if `s ≠ 0` divides `point φ b` for every `R`-point
  `φ`, then `b = s • b'` with `b' ∈ B`. Indeed, `b' = s⁻¹ b` has values
  `s⁻¹ φ(b) ∈ R`.
