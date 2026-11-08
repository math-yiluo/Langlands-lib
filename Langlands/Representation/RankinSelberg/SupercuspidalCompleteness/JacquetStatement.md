# The Jacquet module of the Gelfand–Graev representation (statement)

Internal proposition used in the proof of
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`. The definition supplies no
proof.

## Statement

`GelfandGraevJacquetStatement` has these hypotheses:
- every prime `p` and every `F : PadicField p`, with the canonical topology, valuation and
  local-field structure;
- every unitary additive character `ψ`;
- every `n` and every block shape `B` of `n + 1`.

It asserts that there exists an equivalence of representations of the product Levi
`B.Levi F = ∏ GL_(B.size i)(F)` between:
- `F.canonicalTopologicalData.normalizedJacquet B (gelfandGraev ψ n)`, the coinvariants of the
  Gelfand–Graev representation `c-Ind_N^G ψ` under the unipotent radical of the upper block
  parabolic, with the Levi action normalized by `δ_P^(-1/2)`;
- `leviGelfandGraev B ψ.complex`, the Gelfand–Graev representation `c-Ind_{N_M}^M ψ_M` of the
  Levi, for the product of the blockwise standard characters.

## Provenance

This is the classical computation of the Jacquet module of a Gelfand–Graev representation,
derived here for `GL_n`; see Bushnell–Henniart's treatment of generalized Whittaker models and
Bernstein–Zelevinsky's geometric lemma. Only the open `N`–`P` double coset contributes. The
normalization by `δ_P^(-1/2)` cancels the modulus that comes from integrating over the unipotent
radical, up to a character twist that is absorbed by multiplying functions by that character.
