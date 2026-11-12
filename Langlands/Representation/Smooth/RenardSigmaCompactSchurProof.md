# Schur's lemma for sigma-compact groups

Author: Worker 138. Namespace `Langlands.Renard.Smooth`.

The theorem `sigmaCompactSchur` proves exactly the published proposition `SigmaCompactSchurStatement`, Renard III.1.8. The source is David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, printed p.62 / PDF p.68, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The proof follows the source's countable-orbit argument and then uses the published `Langlands.countableDimensionalSchur`. It counts the orbit without choosing coset representatives: a smooth vector's orbit map is locally constant (`Hecke.orbitMap_locallyConstant`), hence has finite image on each compact subset. A countable compact covering of the group makes the whole orbit countable (`sigmaCompact_countable_orbit`). The orbit of a nonzero vector spans an irreducible representation, by the published `span_range_orbit_eq_top`. The rank bound for a span therefore gives `Module.rank ℂ V ≤ Cardinal.aleph0` (`sigmaCompact_irreducible_rank_le_aleph0`). These two helper lemmas are implementation results derived from the same argument.

Countable-dimensional Schur makes every intertwining endomorphism scalar. Between two irreducible representations every intertwiner is bijective or zero. In the bijective case its actual linear map defines a representation equivalence, contradicting the stated absence of an equivalence. The source and target carrier universes remain independent. No separability, second countability, admissibility or additional hypothesis is assumed. The published statement and its imports are unchanged.
