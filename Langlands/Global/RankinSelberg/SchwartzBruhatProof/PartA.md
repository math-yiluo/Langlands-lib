# The restricted-tensor description of `S(𝔸^n)`

Module `Langlands.Global.RankinSelberg.SchwartzBruhatProof.PartA`, namespace
`Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof`. It proves clause 1 of
`Langlands.Global.RankinSelbergGlobal.SchwartzBruhatStatement`:

```
theorem schwartzBruhat_eq_restricted :
    schwartzBruhat F n = restrictedSchwartzBruhat F n
```

## Provenance

This is Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §C.3, printed
p.553 (registered as `getz-hahn-2024-automorphic-representations`). There
`S(W(𝔸_F)) = S(W(F_∞)) ⊗ C_c^∞(W(𝔸_F^∞))` is identified with the restricted tensor product. The
argument is the one recorded in the statement's Markdown. `C_c^∞(𝔸_f^n)` is spanned by indicators of
cosets `a + ∏_v ϖ_v^(k_v) 𝒪_v^n`, each a restricted pure tensor. Conversely, the finite part of a
restricted pure tensor is locally constant with compact support.

## Proof

`schwartzBruhat_le_restricted` (`⊆`). Take a spanning pure tensor `Φ_∞ ⊗ Φ_f`.
`exists_eq_sum_latticeVec` (module `Lattice`) writes
`Φ_f = Σ_(a ∈ s) Φ_f(a) 1_(a + L_m^n)`. So `Φ_∞ ⊗ Φ_f` is a linear combination of the functions
`Φ_∞ ⊗ 1_(a + L_m^n)`. `isRestrictedPure_mul_cosetIndicator` shows that each of these is a
restricted pure tensor. Choose a finite `S` outside of which `m v = 0` and every coordinate of `a`
is integral (`exists_finset_adapted`), and take the local factors
`Φ_v = 1_(a_v + L_v(m v)^n)` for `v ∈ S`. For `x` integral outside `S`,
`x_f - a ∈ L_m^n` holds exactly when `x_v - a_v ∈ L_v(m v)^n` for all `v ∈ S`
(`sub_mem_latticeVec_iff`), and `Finset.prod_boole` turns the product of indicators into one
indicator. For `x` not integral outside `S`, both sides vanish:
`mem_integralVecOutside_of_sub_mem` shows that `x_f - a ∈ L_m^n` forces integrality outside `S`.

`restricted_le_schwartzBruhat` (`⊇`). Take a spanning restricted pure tensor with data
`Φ_∞, S, (Φ_v)`. Its finite part is `restrictedFinitePart n S Φloc`, the function
`z ↦ if z ∈ integralVecOutside n S then ∏_(v ∈ S) Φ_v(z_v) else 0`. Here `integralVecOutside n S`
is the open and closed subgroup of vectors that are integral at every place outside `S`. The
finite part is:

- locally constant (`isLocallyConstant_restrictedFinitePart`): `isLocallyConstant_ite_of_isClopen`
  together with `isLocallyConstant_finset_prod` and continuity of the evaluations `z ↦ z_v`;
- compactly supported (`hasCompactSupport_restrictedFinitePart`): choose for each `v ∈ S` a `k_v`
  with `tsupport Φ_v ⊆ L_v(k_v)^n` (`exists_additiveLattice_pi_of_isCompact`). The support then
  lies in the compact set `L_m^n` with `m v = max(k_v, 0)` on `S` and `m v = 0` elsewhere.

The restricted pure tensor is then the pure tensor `Φ_∞ ⊗ restrictedFinitePart n S Φloc`.

## Other declarations

- `isLocallyConstant_ite_of_isClopen`, `isLocallyConstant_finset_prod`: generic facts about
  locally constant functions.
- `localLatticeVec n v k = L_v(k)^n ⊆ F_v^n`, with `mem_localLatticeVec`, `coe_localLatticeVec`,
  `isOpen_localLatticeVec` and `isCompact_localLatticeVec`.
- `integralVecOutside n S`, with `mem_integralVecOutside`, `mem_integralOutside_iff` (it is the
  finite-coordinate form of the Library's `integralOutside F n S`),
  `isOpen_integralVecOutside` and `isClosed_integralVecOutside`.
