# The transcendental case of the unit enlargement

`Enlargement.caseB`: the enlargement when the residue `α` of the unit `ℓ` is transcendental over
`κ_D`. It is stated for an algebra `D → L` (local, flat), like `caseA`, and uses only the standard
axioms.

1. Let `𝔐 ⊂ D[X]` be the preimage of `𝔪_L` under `X ↦ ℓ`. Then `𝔐 = 𝔪_D D[X]`. If `f(ℓ) ∈ 𝔪_L`,
   then `f̄(α) = 0`, so `f̄ = 0` because `α` is transcendental, and all coefficients of `f` lie in
   `𝔪_D` (`Ideal.mem_map_C_iff`).
2. `D' = D[X]_𝔐` is local with `𝔪_{D'} = 𝔪_D D'`, which is nilpotent. So `D'` is Artinian, and it
   is essentially of finite type over `k`.
3. The map `D' → L` is the localization of `X ↦ ℓ`: elements outside `𝔐` map to units. It is
   local, and `L` is flat over `D'` (`flat_of_map_maximalIdeal`).
4. Take `v = X/1`, so `ψ'(v) = ℓ`, and `u = v^p`, so `ψ'(u) = ℓ^p` and `dū = 0`.
5. `κ_{D'}` is generated as a fraction field by `T = v̄`, and `T` is transcendental over `κ_D`.
   - Fractions: `res(f/s) = f̄(T)/s̄(T)`.
   - Transcendence: if `f̄(T) = 0`, then `f ∈ 𝔐`, so `f̄ = 0`.
   By `kaehler_basis_adjoin_transcendental`, the `d(b̄_i)` together with `dT` form a basis of
   `Ω_{κ_{D'}/k}`. Here `r = 1`.
