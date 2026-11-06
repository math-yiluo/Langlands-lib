# Local finiteness of the open-cell gamma

This is an internal prerequisite for the source gamma integral in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
I.1, printed p.240 / PDF p.6, the second formula (2) and the gamma display
immediately before Remark (3). The cited source is `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The argument here is derived from the existing local open-cell integration
theorem; the source does not isolate this local finiteness lemma.

Let `G` be a topological group with its Borel measurable structure, let `P,V`
be subgroups whose inherited topologies are locally compact and second
countable, and equip all three groups with the displayed Haar measures.
The ambient measure is also right invariant. Assume that the actual map
`(p,v) ↦ p v⁻¹` is an open embedding. Let `K` be a compact open subgroup.
All carriers have arbitrary universes. No ambient separation assumption beyond
those in the displayed hypotheses is added.

`measure_inter_range_eq_mul_openCellConstant` applies a supplied local range
integration formula to the indicator of `K`. Measurability follows from
openness of `K` and continuity of multiplication and inversion. Interchanging
the two lower integrals gives
`μ(K ∩ range(cell)) = c * openCellConstant μP μV K`.
This identity alone does not require ambient Haar or right invariance.

`openCellConstant_ne_zero_ne_top_of_isOpenEmbedding` obtains the finite
positive coefficient `c` from `exists_lintegral_range_openCellMap`. The set
`K ∩ range(cell)` is open and contains one, since `cell(1,1)=1`, so its
ambient Haar mass is nonzero. Its mass is finite by containment in compact
`K`. The preceding identity excludes both zero and infinity for the existing
`openCellConstant`, at precisely the originally supplied subgroup Haar scales.

The open cell need not be conull. This result supplies local finiteness and
positivity; a global integration formula still requires the separate
conullness theorem. The generic subgroups must be identified with the desired
parabolic and opposite radical in any application. No special compact,
Iwasawa factorization, reductive unimodularity or Levi independence is
constructed here.
