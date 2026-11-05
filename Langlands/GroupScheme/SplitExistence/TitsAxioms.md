# Axiom T3 for the Chevalley group

Author: Worker 1398.

`tits_mul_mem`: for a simple root `i`, a representative `n = n_i t` of `s_i`, `m ∈ N` and
`g = u' t' x_i(a) ∈ B`, `n g m ∈ B m B ∪ B (n m) B`. First `n u' n⁻¹ ∈ U'_i` (`n_i` permutes the
positive roots other than `i`, Mathlib `IsPos.reflectionPerm`) and `n t' n⁻¹ ∈ T`. Then
`m⁻¹ U_{±i} m` are the root groups of `±w(i)` (`IsRootPerm`); if `m⁻¹ U_i m` is positive,
`n x_i(a) m = (n m)(m⁻¹ x_i(a) m)`. Otherwise `m⁻¹ U_{-i} m ⊆ B`, and for `a ≠ 0` the rank-one
identity `x_{-i}(u) = x_i(u⁻¹) α_i^∨(-u⁻¹) n_i x_i(u⁻¹)` rewrites
`n x_i(a) m = x_i(u⁻¹) α_i^∨(-u⁻¹) ρ m (m⁻¹ x_{-i}(c) m)` with `ρ ∈ T`, an element of `B m B`.
This is Steinberg, *Lectures on Chevalley groups*, §3, Lemma 25, in the form of the axiom
`IsConcreteTits.mul_mem`.
