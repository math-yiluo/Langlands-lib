# Galois twisting preserves norm-one adelic points (Lemma C)

Statement-only helper module for the proof of `GaloisBorelTwistingStatement` (Task 5268). The statement is proved in module `AdelicGaloisTwistNormOneProof`.

`TwistPointNormOneStatement`: for a finite Galois extension `L/F` of number fields,
`σ ∈ Gal(L/F)`, an affine group `H` over `L`, and an adelic point `p ∈ H(𝔸_L)` in the
norm-one subgroup `H(𝔸_L)^1` (all `|χ(p)| = 1` for characters `χ` of `H` over `L`), the
twisted point `twistPoint F L σ H p` lies in the norm-one subgroup of `H^σ`, the base change
of `H` along `Spec σ`.

Proof outline. Since `Spec σ` is an isomorphism, `Over.pullback (Spec σ)` is fully faithful
(its counit is an isomorphism), so by `Functor.FullyFaithful.mapGrp` every character `ψ` of
`H^σ` is the base change of a character `χ₀` of `H` (up to the canonical isomorphism of the
base-changed multiplicative group). On points, `ψ(twistPoint p) = σ̃(χ₀(p))` in `𝔸_L^×`,
and `|σ̃(y)| = |y|` by `AdeleGalois.full_idelesMap`. Hence `|ψ(twistPoint p)| = 1`.

Used for clause 4 of `IsGaloisBorelTwist` (norm-one points of the minimal standard
parabolic).
