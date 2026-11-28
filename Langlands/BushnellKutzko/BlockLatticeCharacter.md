# Trace characters of finite lattice quotients

For an integral submodule `Λ ⊆ 𝔄` and `N ≥ 0`, `SplitBlocks.finite_latticeQuotient`
proves finiteness of `Λ / (Λ ∩ 𝔓ᴺ)` by identifying it with the image of `Λ` in
`𝔄 / 𝔓ᴺ`.

For a character `ψ_F` satisfying `IsBKAdditiveCharacter`, integral factors `e₁`,
`e₂`, and `w ∈ 𝔓¹⁻ᴺ`, `SplitBlocks.latticeBlockCharacter` descends the trace
character `y ↦ ψ_A(e₁ y e₂ w)` to this quotient. Multiplication of the filtration
steps places the trace argument in `𝔓¹` when `y ∈ 𝔓ᴺ`. This is the basic
filtration duality used in Bushnell–Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (3.1.19) and the proof of (8.2.26).
