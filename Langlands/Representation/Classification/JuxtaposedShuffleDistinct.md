# Distinct shuffles give inequivalent shuffle tensors

Helper module for the juxtaposed case of Zelevinsky 1980, Proposition 4.6
(task 0c90f7e4-78fa-43fd-8736-238bb3e8617d). It contains no statement of its own
from the literature. In Zelevinsky's proof, each shuffle tensor `τ_S` occurs in the
Jacquet module of `⟨Δ₀⟩ × ⟨Δ₁⟩` with multiplicity one. This module supplies the
input that makes the multiplicities at most one: different shuffles give
inequivalent tensors.

Notation: `A` is a supercuspidal representation of `GL_r`. For a set
`S ⊆ Fin (q + l)`, the shuffle tensor `τ_S` is the external tensor product of
`shuffleFactors F T A.obj (q + l) hr S l 0`, whose factor `k` is `ν^(e_S(k)) A`
with `e_S = shuffleExponent S l 0`.

## Declarations

- `eq_of_segmentFactor_equiv`: if `ν^a A` and `ν^b A` are equivalent for natural
  numbers `a, b`, then `a = b`. Proof: by `cuspidalDatum_eq_of_equiv` (with the identity
  coordinate bijection), the cuspidal data of the two twists are equal, so the data
  `ν^a ρ` and `ν^b ρ` of `ρ = [A]` are equal. Then
  `cuspidalDatum_integralTwist_injective` gives `a = b`.
- `eq_of_shuffleTensor_equiv`: if `#S = #S' = q` and `τ_S` is equivalent to
  `τ_{S'}`, then `S = S'`. Proof: fix a position `k`. Restrict the equivalence to
  the copy of `GL_r` in block `k` (`equivComp` along `MonoidHom.mulSingle`). There
  the two tensors are acted on through factor `k` only (`external_mulSingle_tprod`).
  So `nonempty_equiv_of_factor_actions`, which uses that the factors are
  irreducible and nonzero, gives `ν^(e_S(k)) A ≃ ν^(e_{S'}(k)) A`. Both exponents are
  natural numbers (`exists_natCast_shuffleExponent`), so they are equal by
  `eq_of_segmentFactor_equiv`. Equal exponents at every position give `S = S'` by
  `eq_of_shuffleExponent_eq`.
