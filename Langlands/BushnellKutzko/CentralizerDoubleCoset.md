# Centralizer filtrations from a double coset `J B_β^× J`

Let `F` be a nonarchimedean local field, `V` a finite-dimensional `F`-vector
space, `𝓛` an `𝔬_F`-lattice chain in `V` and `𝔓^t = 𝓛.endFiltration t`. For
`β ∈ A = End_F(V)` let `B_β^×` be the group of units commuting with `β`
(`centralizerUnitGroup β`) and `𝔔^t = 𝔓^t ∩ B_β` (`centralizerLattice 𝓛 β t`).
The module shows that a double coset `J B_β^× J`, with `J ⊆ U¹(𝔄)`, determines
`𝔔^t + 𝔓^{t+1}` for every `t ∈ ℤ`. All results are proved.

## Results

- `commute_of_mem_centralizerLattice`, `mem_centralizerLattice_of_commute`:
  membership in `𝔔^t` is membership in `𝔓^t` together with commuting with `β`.
- `exists_units_sub_eq_of_mem_centralizerLattice`: every `x ∈ 𝔔^t` is a
  difference `g − h` of two units of `B_β^×` that lie in `𝔓^t`.
- `centralizerLattice_sup_eq_span`: let `J` be a subgroup of `U¹(𝔄)` and
  `I = J B_β^× J`. Then `𝔔^t + 𝔓^{t+1}` is the `𝔬_F`-span of the elements of
  `I` lying in `𝔓^t`, plus `𝔓^{t+1}`.
- `centralizerLattice_sup_eq_of_doubleCoset_eq`: let `J₁, J₂ ⊆ U¹(𝔄)` be
  subgroups with `J₁ B_{β₁}^× J₁ = J₂ B_{β₂}^× J₂`. Then
  `𝔔₁^t + 𝔓^{t+1} = 𝔔₂^t + 𝔓^{t+1}` for every `t ∈ ℤ`.

## Proofs

For the difference of units, let `ϖ` be a uniformizer of `F`. The scalars
`ϖ^l` with `l ≥ max(t, 0)` lie in `𝔓^{el} ⊆ 𝔓^t`, where `e` is the period of the
chain, and are pairwise distinct. Only finitely
many of the `−ϖ^l` are eigenvalues of `x`, so some `x + ϖ^l` is invertible.
Both `x + ϖ^l` and `ϖ^l` commute with `β`, and `x = (x + ϖ^l) − ϖ^l`.

For the span, the difference of units shows that `𝔔^t` lies in the span.
Conversely, let `g = j₁ b j₂ ∈ I ∩ 𝔓^t` with `j₁, j₂ ∈ J` and `b ∈ B_β^×`.
Since `j₁^{±1}, j₂^{±1} ∈ 𝔄`, the element `b = j₁⁻¹ g j₂⁻¹` lies in
`𝔓^t ∩ B_β = 𝔔^t`. Also
`g − b = (j₁ − 1) b j₂ + b (j₂ − 1) ∈ 𝔓^{t+1}`. The last result follows by
applying the span description to both double cosets.

## Origin

This is the "additive closure" step in the proof of (3.5.1) of Bushnell and
Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
printed p. 117 (PDF p. 129), literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. It is also
the step from (5.7) to (5.8) in the proof of Lemma (5.2) of Bushnell and
Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994), printed
p. 134 (PDF p. 147), literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`. The
difference-of-units argument shows that the additive closure contains `𝔔^t`.
