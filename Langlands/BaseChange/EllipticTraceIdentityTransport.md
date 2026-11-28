# Transport of an elliptic twisted trace identity

`HasEllipticTraceIdentity σ l π hπ τ` packages the local conclusion of
`Langlands.TraceFormula.CyclicBaseChangeEllipticTraceIdentityStatement` for a fixed
ordinary representation `π` with admissibility proof `hπ`. It requires admissibility of `τ`,
a `σ`-intertwiner `A` for `τ` and a single constant `c ≠ 0`. For every pair of Haar measures
the twisted trace associated with `A` equals `c` times the ordinary trace on concordant
Schwartz–Bruhat pairs. The twisted test is supported in the `σ`-elliptic set. The ordinary
test is supported in the regular elliptic set with determinants in the norm group.

## Change of algebra and representation

Let `ε : R₁ ≃ₐ[F] R₂` be a homeomorphic isomorphism of topological algebras over a
topological field `F`, with `ε ∘ σ₁ = σ₂ ∘ ε`. Write `κ` for the induced continuous
group isomorphism from `GL_n(R₁)` to `GL_n(R₂)`. Assume the matrix groups over `F`,
`R₁` and `R₂` are Hausdorff, locally compact and totally disconnected. Given an
equivalence `B : τ₁ ≃ τ₂ ∘ κ`, `ellipticTraceIdentity_transport` carries an elliptic
twisted trace identity for `τ₂` to one for `τ₁` with the same constant.

The proof transports admissibility first along `κ`
(`isAdmissible_comp_continuousMulEquiv`) and then along `B`
(`isAdmissible_iff_of_equiv`). Pulling the `σ₂`-intertwiner back along `κ` gives
`SigmaIntertwiner.pullbackRingEquiv`. Conjugating that map by `B` gives the
`σ₁`-intertwiner on `τ₁` (`SigmaIntertwiner.transport`).

For a Haar measure `μ` on `GL_n(R₁)` and a test `φ`, use `κ_*μ` and `φ ∘ κ⁻¹` on
`GL_n(R₂)`. The ordinary Haar measure and test `f` stay fixed. The required support
of the twisted test follows from `isSigmaElliptic_generalLinearRingEquiv_iff`.
The norm images on units agree by `normUnitsRange_algEquiv`, which uses
`Algebra.norm_eq_of_algEquiv` in both directions. `concordanceRingEquiv` with the
identity on `F` and `ε⁻¹` on the other algebra transports concordance. The pushed
measure returns to `μ` after the inverse pushforward.

Apply the trace identity for `τ₂` to these data. The twisted trace for `τ₁`
agrees with that for `τ₂ ∘ κ` by `twistedDistribution_eq_of_equivalent`,
with the intertwiner conjugated along `B`. The latter trace agrees with the
twisted trace for `τ₂` on `φ ∘ κ⁻¹` by `twistedDistribution_comp_equiv`.

`ellipticTraceIdentity_transport_comp` applies this result to pullbacks
`τᵢ = ρᵢ ∘ ψᵢ`. An equivalence of `ρ₁` with `ρ₂ ∘ c` induces the required
equivalence of `τ₁` with `τ₂ ∘ κ` when the homomorphisms satisfy
`c ∘ ψ₁ = ψ₂ ∘ κ`. The proof keeps the underlying linear equivalence and checks
the intertwining relation at each matrix.

This transport is derived from the local conclusion of the elliptic trace identity,
the Library's change of variables for concordance in `ConcordanceRingEquiv`, and
the change of variables for twisted traces in `TwistedLocalGroupTransport`.
