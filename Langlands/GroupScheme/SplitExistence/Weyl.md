# Weyl elements

Author: Worker 1398.

* Identities in `SL₂(R)`: `w = u(1) l(-1) u(1)` (`sl2Weyl_eq`), `w diag(t,t⁻¹) = diag(t⁻¹,t) w`,
  `w² = diag(-1,-1)`, and `l(u) = u(u⁻¹) diag(-u⁻¹, -u) w u(u⁻¹)` for a unit `u` (`sl2Lower_eq`),
  each checked on matrix entries.
* `corootChar i t : x ↦ t ^ ⟨x, i^∨⟩`, `wn i = φ_i(w)`, `wn_eq : n_i = x_i(1) x_{-i}(-1) x_i(1)`,
  `wn_weight` (from the datum), `reflectChar i χ = χ ∘ s_i`, `wn_mul_torusHom : n_i t(χ) =
  t(χ ∘ s_i) n_i`, `wn_mul_self : n_i² = α_i^∨(-1)`, the rank-one identity
  `x_reflectionPerm_self : x_{-i}(u) = x_i(u⁻¹) α_i^∨(-u⁻¹) n_i x_i(u⁻¹)`, and `wn_conj_x`.
Internal lemmas following the rank-one computations of Steinberg, *Lectures on Chevalley
groups*, §3.
