# The averaging weight and the target function on `N K⁰(f)`

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4: the character `ω_f` of formula (11) and the target function of
formula (12), printed pages 328 and 329, transported to the Library's dual coordinates).

Throughout, `ω` is a character of `F^×` with `TrivialOnPrincipalUnits ω f`, i.e. trivial on
`1 + 𝔭^f`, and `f ≥ 1`; `K⁰(f)` is the first-column line subgroup (`FirstColumnLine`).

- `firstEntryUnit hf k hk`: the entry `k₀₀` of `k ∈ K⁰(f)` as a unit of `F`.
- `omega_eq_of_sub_mem`: `ω(a) = ω(b)` when `a = b + y` with `y ∈ 𝔭^f` and `b⁻¹` integral.
- `firstEntry_mul_principal`, `firstEntry_unipotent_mul`: `(k l)₀₀ ≡ k₀₀` for `l` in the
  published principal congruence subgroup of level `f`, and `(n k)₀₀ ≡ k₀₀` for integral upper
  unipotent `n`, modulo `𝔭^f`.
- `firstColumnWeight ω hf`: `w(k) = ω(k₀₀)⁻¹` on `K⁰(f)` and `0` elsewhere;
  `firstColumnCharacter ω hf`: `b(k) = ω(k₀₀)⁻¹` on `K⁰(f)` and `1` elsewhere;
  `firstColumnWeight_mul_inv`: `w b⁻¹` is the indicator of `K⁰(f)`;
  `firstColumnWeight_mul_principal`: `w` is right invariant under the principal congruence
  subgroup of level `f`.
- `firstColumnTarget ω hf ψN`: for a character `ψN` of the upper unipotent group that is trivial
  on integral points, the function equal to `ψN(u) ω(k₀₀)` at `u k` (`u ∈ N`, `k ∈ K⁰(f)`) and to
  `0` off `N K⁰(f)`. It is defined by choosing a decomposition; `firstColumnTarget_mul` shows that
  the value does not depend on the choice, since two choices differ by an integral unipotent
  element.
- `firstColumnTarget_unipotent_mul`: left `(N, ψN)`-equivariance;
  `firstColumnTarget_mul_principal`: right invariance under the principal congruence subgroup;
  `firstColumnTarget_support`: the target vanishes off `N K⁰(f)`.
