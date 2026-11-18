# Adjoint lattices and the critical exponent

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, (1.4.1), printed p. 35, and
Definitions (1.4.3), (1.4.5)–(1.4.6), printed p. 36 (PDF pp. 47–48).

This module reuses the published `LatticeChain O K V` and its `endFiltration`.
The general ring-and-field parameters allow the same definitions over `F`
and over extension fields with their integral closures as rings of integers.

- `adjointMap O β` is the `O`-linear map `x ↦ βx − xβ`, implemented as the
  difference of left and right multiplication maps.
- `adjointLattice 𝓛 β k` is `𝔑_k`: the intersection of `𝔄 = 𝔓^0` with the
  preimage of `𝔓^k` under that map.
- `centralizerLattice 𝓛 β k` is the intersection of the existing `𝔓^k` with
  the kernel of `a_β`. This is an auxiliary expression for `𝔓^k ∩ B`, not a
  new radical filtration. When `E = K[β]` is a field, the kernel is its
  centralizer `End_E(V)`. Under normalization, the published
  `SubfieldOrderStatement` identifies these intersections with `𝔔^k`.
- `criticalIndexSet 𝓛 β` is the set of integers for which `𝔑_k` is not
  contained in `𝔅 + 𝔓`. Sum of lattices is the supremum of submodules.
- `criticalExponent 𝓛 β : WithBot ℤ` is `⊥ = −∞` when
  `Algebra.adjoin K {β} = ⊥`, which says `K[β] = K`. Otherwise it is the
  integer supremum of `criticalIndexSet`, embedded in `WithBot ℤ`.

The last definition is total, including when `K[β]` is not a field or the
order is not normalized. Its supremum in those extra cases carries no
mathematical assertion. Under the hypotheses of BK93 §1.4, T2
(`AdjointExactnessStatement`) separately states that the index set is
nonempty and bounded above and that this definition equals its greatest
element. No existence or exactness assertion is a definition field or
hypothesis.
