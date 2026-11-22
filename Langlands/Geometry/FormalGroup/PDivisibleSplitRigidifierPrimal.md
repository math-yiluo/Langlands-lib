# Primal block of the original split rigidifier

For two affine coefficient rings mapping to a common ring, the source and
target are the actual pullbacks of the split towers. A proof of
`FiniteCartierDualExactnessStatement` supplies the dual towers in each
split product. `pullbackPrimalBlock` includes the primal source, applies
the rational map on the full towers and projects to the primal target.
Both inclusion and projection are the pullbacks of the original integral
maps, viewed in rational Hom.

`splitQuasiIsogenyOnBaseChange_hom_fst` proves that the primal projection
commutes with the actual transported split map. The target split comparison
cancels its inverse and the split map's first block is the primal map.
As the original primal projection retracts the inclusion, the block
extracted from the transported split rigidifier is the original primal
quasi-isogeny's forward map, with any common nonzero `ℚ_p` multiplier.

Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321), uses the
primal pair before (6.17). This identity supplies the corresponding
projection on the actual special-fibre tower in Harris (1997), Appendix,
printed pp. 113–114 (PDF pp. 39–40), C1(iii) and (A.1)–(A.2).
