# The open orbit piece of the Jacquet module of a Gelfand–Graev representation (statement)

Draft by Worker 1832 for task `d7c75f29-8641-4f6e-9a08-aaa69f1db69c`. This is an internal
interface for the proof of `GelfandGraevJacquetStatement`. The proposition supplies no proof.

## Definitions

- `parabolicNormalizedJacquet T B ρ`: for a representation `ρ` of the upper block parabolic
  `P = B.parabolic F`, the Levi `M = B.Levi F` acts on the coinvariants of `ρ` under the
  unipotent radical `U = B.unipotentRadical F`. The action goes through the Levi section into `P`
  and is scaled by `δ_P^(-1/2)`, where `δ_P` is `T.leviModulus B`. It is built with
  `Jacquet.normalizedActionOfModulus`, exactly as `T.normalizedJacquet B` is.
- `normalizedJacquet_eq_parabolicNormalizedJacquet`: for a representation `ρ` of `GL_n(F)`,
  `T.normalizedJacquet B ρ` equals `parabolicNormalizedJacquet T B` applied to the restriction of
  `ρ` to `P`. This holds by definition (`rfl`).

## Statement

`GelfandGraevOpenPieceStatement` has these hypotheses:
- every prime `p` and every `F : PadicField p`, with the canonical topology, valuation and
  local-field structure;
- every unitary additive character `ψ`;
- every `n` and every block shape `B` of `n + 1`.

Write `N` for the upper unipotent subgroup of `GL_(n+1)(F)`, `P` for the upper block parabolic
and `w = B.reverseMatrix F` for the block-reversal matrix. Let `H` be the subgroup
`Geometric.orbitStabilizer N P w = P ∩ w N w⁻¹`. The map
`Geometric.stabilizerToInducing N P w` sends `h ∈ H` to `w⁻¹ h w ∈ N`. The proposition asserts
that there exists an equivalence of representations of `M` between:
- `parabolicNormalizedJacquet` of the compact induction `c-Ind_H^P (ψ_N ∘ Ad(w⁻¹))`, where `ψ_N` is
  the Gelfand–Graev character `gelfandGraevCharacterRepresentation ψ n`;
- `leviGelfandGraev B ψ.complex`, the Gelfand–Graev representation `c-Ind_{N_M}^M ψ_M` of the
  Levi.

## Provenance

In the Mackey filtration of `c-Ind_N^G ψ_N` restricted to `P`, the piece of the double coset
`N w⁻¹ P` is `c-Ind_H^P (ψ_N ∘ Ad(w⁻¹))`. For the block-reversal representative this double coset is
the open one. `H` is the image of `N_M` under the Levi section, and the character becomes
`ψ_M` (`Whittaker.openStabilizerEquiv`). The computation of the Jacquet module of this piece is
the open-orbit step of the classical computation of the Jacquet module of a Gelfand–Graev
representation; see Bernstein–Zelevinsky's geometric lemma and Bushnell–Henniart's treatment of
Whittaker models. The formulation is internal.
