# Lifting a relative wave packet to a wave packet of the same parabolic

Module `Langlands.Global.AdelicWavePacketParabolicAmbientLiftStatement` states
`WavePacketParabolicAmbientLiftStatement`. It proves nothing.

| Declaration | Kind | Provenance |
| --- | --- | --- |
| `WavePacketParabolicAmbientLiftStatement` | statement | derived; Getz–Hahn §10.5, Lapid 2011 §3 |

## Statement

The binders are those of the published `Langlands.Global.WavePacketAmbientLiftStatement`
(module `Langlands.Global.AdelicWavePacketAmbientLiftStatement`), unchanged: a number field
`F : Type`; `G` affine, locally of finite type, with `IsConnectedReductive G`; a presented
parabolic `(P, M, U, A, p, iU, l, a, r, hA, hT)` with `LeviSubgroup.IsGeometricUnipotentRadical
iU`; a subgroup `K` with `hK : IsIwasawaCompact p K`; `rho`, `hsmooth`, `hcalc`; real linear
coordinates `eG : ℝ^m ≃ X^*(G) ⊗ ℝ` and a smooth compactly supported `b : ℝ^m → ℂ`.

Conclusion: for every `Θ` with `IsRelativeWavePacket hK rho hsmooth hcalc iU l r hA hT Θ`, the
function `g ↦ ambientWavePacketProfile eG b g * Θ g` satisfies
`IsParabolicWavePacket hK rho hsmooth hcalc iU l r hA hT`. Here
`ambientWavePacketProfile eG b g = ∫ b(z) · g^{i eG(z)} d(spectralMeasure m)(z)` (published in
`Langlands.Global.AdelicWavePacketAmbientLiftStatement`) and `IsParabolicWavePacket` is the
predicate of `Langlands.Global.AdelicNonAssociateWavePacketOrthogonality`: a wave packet of the
same presented parabolic `P` over all of `i𝔞_P^*`, for the same `hK`, `iU`, `l`, `r`, `hA`,
`hT`.

## Relation to the published lift

`WavePacketAmbientLiftStatement` has the same hypotheses and concludes `IsWavePacket F G K rho
hsmooth hcalc (fun g => ambientWavePacketProfile eG b g * Θ g)`, whose definition quantifies a
presented parabolic existentially. It therefore does not say that the lift is a wave packet of
`P`. The orthogonality of non-associate parabolics on `[G]`
(`RelativeWavePacketOrthogonalityStatement`, Task 7950) needs the lifts of the wave packets of
`P` and `P'` to be wave packets of `P` and `P'` themselves, to apply
`NonAssociateWavePacketOrthogonalityStatement`, whose hypothesis concerns the Levi subgroups of
these two parabolics. The statement here is that stronger form. It implies the published one
(unpack `IsParabolicWavePacket`, add the closed immersion `iU ≫ p` and the radical hypothesis);
that implication is not proved here.

## Why it holds (explanatory, not proved here)

Getz–Hahn, *An introduction to automorphic representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, §10.5, (10.22)–(10.24), printed pp.281–282 (PDF
pp.293–294), integrate Eisenstein series over `i(𝔞_M^G)^*`; Lapid 2011
(`lapid-2011-asymptotic-inner-product-truncated-eisenstein`), §3, printed p.314 (PDF p.323),
integrates over all of `i𝔞_P^*`. Write `𝔞_P^* = (𝔞_M^G)^* ⊕ 𝔞_G^*`, the second summand
pulled back from `G`. For `ν ∈ 𝔞_G^*` the Eisenstein series satisfies
`E(φ, λ + iν)(g) = g^{iν} E(φ, λ)(g)`: in the defining sum `∑_γ φ_λ(γg)` each term is multiplied
by `(γg)^{iν} = g^{iν}`, because the height of `γg` projects to the logarithm of `γg` on `G` and
rational points have trivial logarithm; the identity passes to the meromorphic continuation by
uniqueness. (The Markdown of the published `WavePacketAmbientLiftStatement` derives this shift
from Bernstein–Lapid 2024, §2.1–2.2, (2.1).) So if
`Θ(g) = ∫ ∑_j c_j(x) E_j(i e(x))(g) dx` with `e` coordinates on `(𝔞_M^G)^*`, then in the product
coordinates `(x, z) ↦ e(x) + eG(z)` of `𝔞_P^*` and with coefficients `c_j(x) b(z)`,
`∫∫ ∑_j c_j(x) b(z) E_j(i e(x) + i eG(z))(g) dx dz = (∫ b(z) g^{i eG(z)} dz) · Θ(g)` by Fubini.
The new coefficients are smooth and compactly supported, the inducing forms `v j`, the
continuations `E j`, their domain `D` and the regularity witnesses are unchanged, and the
product of the two spectral measures is the spectral measure of the product coordinates. This
is the construction in Worker 3657's checked draft proof of the published lift (shared draft of
Task 3657, `AdelicWavePacketAmbientLiftProof.lean`), which produces the data of the same
parabolic.

## Scope

The statement concerns functions on `G(𝔸)`. It does not assert that the profile is nonzero or
square integrable, nor any statement on a quotient.
