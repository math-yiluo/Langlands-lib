# Rational characters of the preimage of a subgroup in a central cover

Author: Worker 1413.

Module `Langlands.GroupScheme.SimplyConnected.CoverPreimageCharacters`,
namespace `Langlands.GroupScheme.CoverPreimage`. Internal helpers for clause 4
of the reduction
[`SplitTorusCentralizerCoverPreimageReduction`](SplitTorusCentralizerCoverPreimageReduction.md).
They introduce no literature assertion.

Notation. `f = π ≫ d : C ⟶ D ⟶ G`, `j : M ⟶ G`. The preimage
`M' = subgroupIntersection (π ≫ d) j` has projections
`j' = subgroupIntersectionFst (π ≫ d) j : M' ⟶ C` and
`p = subgroupIntersectionSnd (π ≫ d) j : M' ⟶ M`. The derived part
`D ×_G M = subgroupIntersection d j` has projections to `D` and `M`.

- `prodInr_snd`: the second inclusion of a product followed by the second
  projection is the identity.
- `toDerivedPart π d j : M' ⟶ D ×_G M` is the map into the pullback induced by
  `j' ≫ π` and `p`. It satisfies `toDerivedPart_fst` and `toDerivedPart_snd`.
- `toDerivedPart_isPullback`. The square formed by `j'`, `toDerivedPart`, `π`
  and the projection `D ×_G M ⟶ D` is cartesian on underlying schemes, by
  pullback pasting (Mathlib's `IsPullback.of_right`) from the two
  intersection squares.
- `isCentralFppfCover_toDerivedPart`: if `π` is a central fppf cover and `j`
  is monomorphic, then so is `toDerivedPart π d j`
  (`IsCentralFppfCover.of_isPullback`).
- `isCentralFppfCover_of_isCentralIsogeny`: over a field, a central isogeny is
  a central fppf cover. A finite morphism is quasi-compact, and the published
  `IsCentralIsogeny.exists_pow_eq_one_kernel` gives the exponent.
- `exists_nsmul_eq_characterRestrict`. Assume `π` is a central fppf cover, `d`
  and `j` are monomorphic, `i : Z ⟶ G` is central with `centralProduct i d`
  a central fppf cover, and `iM ≫ j = i`. Then every `χ'` in
  `rationalCharacters M'` has `n • χ' = characterRestrict p χ` for some
  `n > 0` and some `χ` in `rationalCharacters M`. Descend `N • χ'` through
  `toDerivedPart` to `ψ` on `D ×_G M`
  (`exists_characterRestrict_eq_nsmul_of_fpqc`, [toolkit](CoverPreimageToolkit.md)).
  Then descend `N₂ •` (`ψ` composed with the second projection) through the
  restricted product `Z × (D ×_G M) ⟶ M`
  ([`CoverPreimageCentralProduct`](CoverPreimageCentralProduct.md)) to `χ`.
  The projection `D ×_G M ⟶ M` is the second inclusion followed by the
  restricted product (published `prodInr_prodHom`), and `p` is
  `toDerivedPart` followed by that projection. Hence
  `characterRestrict p χ = (N₂ * N) • χ'`.

This replaces the Galois-averaging argument sketched in the Markdown of
`SplitTorusCentralizerCoverPreimageStatement`: both descents are fppf descents
of homomorphisms to `𝔾ₘ` that kill a torsion kernel.
