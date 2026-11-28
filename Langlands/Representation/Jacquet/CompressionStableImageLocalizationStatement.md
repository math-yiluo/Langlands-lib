# Localization at a stabilized compact compression

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, VI.9.1, Proposition, printed p. 197 / PDF p. 203,
identifies the localized endomorphism of \(V^K\) with the restriction of
the compression to \(V_*^K\). Under this identification the canonical
localization map is projection along \(V_0^K\). Appendix C.II, Proposition
(printed p. 279 / PDF p. 285), gives the stable-power localization
identification for module endomorphisms.

`Langlands.Jacquet.CompressionStableImageLocalizationStatement` expresses the
VI.9.1 identification for the actual compressed action
`C = compressedAction ρ hρ K hK g` on the fixed vectors of a smooth complex
representation of a topological group. The group and the carrier have
independent universes. The subgroup `K` is compact open and `g` is an
ambient group point. `CompactCompressionStationaryFrom` supplies the common
stationary threshold and the decomposition with stable image `S` and
power-kernel supremum `D`. In the VI.9.1 application these are the preceding
conclusions of the Proposition for the parabolic and its contracting element.

The unique complex-linear equivalence `Localized C ≃ₗ[ℂ] S` intertwines
`localizedEnd C` with `stableImageAction ρ hρ K hK g`. Composing it with
the canonical map `iota C` gives `S.projectionOnto D h.2.symm`, the
projection onto `S` along `D`.
