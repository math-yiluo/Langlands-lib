# Quotient integrals of functions supported on `H K`

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4: the evaluations `J_i = c W_(i,0)(e)` after (12) and of the right
side of (13), printed page 329), stated for an arbitrary topological group.

`integral_out_of_support`: let `ν` be a compatible quotient measure on `H \ G` for Haar
measures `μ_G`, `μ_H` (the published `IsCompatible`, whose Weil formula holds for compactly
supported continuous complex functions), and let `K` be a compact open subgroup with
`μ_H(H ∩ K) = 1`. If `φ` is continuous, left `H`-invariant and vanishes off `H K`, then
`∫_(H\G) φ(q.out) dν = ∫_K φ dμ_G`.

Proof: `f = 1_K φ` is continuous (`K` is clopen) and compactly supported. Its orbital
average at `g` is `φ(g) μ_H({h : h g ∈ K})`; if `h₀ g ∈ K` this set is the right translate
`(H ∩ K) h₀`, of measure `1` by right invariance of `μ_H`, and if `φ(g) ≠ 0` such an `h₀`
exists. So the orbital average is `φ`, and the Weil formula gives the claim.

For `GL_n(F)` with the Library normalizations (`unipotentHaar_integral`), the hypothesis
`μ_H(H ∩ K) = 1` holds whenever `N ∩ K = N(O)`.
