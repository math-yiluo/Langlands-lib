# A basis adapted to a lattice chain and to bases of its layers

Module `Langlands.BushnellKutzko.SplitTypeJacquet.LayerBasis`. Let `L` be an `𝔬_F`-lattice chain
of period `e` in a vector space `V` over a nonarchimedean local field `F`, and let `b i` be a basis
over the residue field of the layer `L_i / L_(i+1)`, `0 ≤ i < e`, of any rank `d i`.

- `liftVec L b ⟨i, a⟩` is a chosen lift to `L_i` of the basis vector `b i a`
  (`liftVec_mem`, `intervalMk_liftVec`).
- `lattice_le_spanSub`: every `L_j`, `0 ≤ j ≤ e`, is contained in the `𝔬_F`-span `spanSub L b j`
  of the lifts with integral coefficients lying in the maximal ideal on the layers before `j`.
  Conversely, such combinations lie in `L_j` (`sum_smul_liftVec_mem`). The proof of the inclusion
  proceeds through the layers (`lattice_le_spanSub_sup`), with Nakayama's lemma for
  `L_e = 𝔭 L_0` (`lattice_period_eq_smul`).
- `linearIndependent_liftVec` and `span_liftVec`: the lifts form an `F`-basis
  `adaptedBasis L b hϖ` of `V`, indexed by `Σ i, Fin (d i)`. For independence, divide a vanishing
  combination by a coefficient of largest valuation; among the coefficients that are units take
  one in the first possible layer `i`. The part of the combination in layer `i` then lies in
  `L_(i+1)`, contradicting the independence of `b i`.
- `mem_lattice_iff_repr`: for `0 ≤ j ≤ e`, `x ∈ L_j` exactly when all its coordinates in the
  adapted basis are integral and those in the layers before `j` lie in the maximal ideal.
- `toLin_mem_endFiltration_iff`: for `s ∈ {0, 1}`, the endomorphism with matrix `M` in the adapted
  basis lies in `End^s(L)` exactly when all entries of `M` are integral and the entries at
  positions `(p, q)` with `p_1 < q_1 + s` lie in the maximal ideal. Membership in `End^n(L)` can
  be tested on the lattices of one period (`mem_endFiltration_of_lt_period`).

This is the decomposition of a lattice chain along a basis adapted to it, as in C. J. Bushnell and
P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), §1.1, with the
basis built from prescribed bases of the layers.
