# Dynamic parabolic subgroups as semidirect decompositions

Implementation and documentation: Worker 23 (task
`593ef603-6672-4424-976c-14e11e920d9c`).

This module connects the generic adapters of
[`Aubert.General.Parabolic`](Parabolic.md) to the published dynamic subgroups
of the algebraic-groups program. It adds no structure of its own.

## The decomposition

Take a scheme `S`, a group scheme `G` over `S`, and a cocharacter
`χ : (Gm S).toGrp ⟶ G`. For every test object `T : Over S`, the published
`Dynamic.parabolic χ`, `Dynamic.centralizer χ` and `Dynamic.unipotent χ`
(module `GroupScheme.Dynamic.Basic`) have `carrier T`, which is an actual
subgroup of the group of points `T ⟶ G.X`.

* `dynamic_parabolic_le_normalizer χ T` shows that `P(χ)(T)` normalizes
  `U(χ)(T)`. It needs no hypotheses. The forward direction is the published
  `Dynamic.conj_mem_unipotent`; the reverse applies it to `p⁻¹`.
* Assume `[IsSeparated G.X.hom]`. Then `dynamic_isSemidirectDecomposition χ T`
  proves `IsSemidirectDecomposition (P(χ)(T)) (Z(χ)(T)) (U(χ)(T))`. The two
  inclusions are `Dynamic.centralizer_le_parabolic` and
  `Dynamic.unipotent_le_parabolic`. The complement is
  `Dynamic.isComplement'_unipotent_centralizer_of_isSeparated`, the points
  version of Conrad–Gabber–Prasad, Proposition 2.1.8(2). That theorem is in the
  order `U * Z`, so it enters through `IsSemidirectDecomposition.of_isComplement'_symm`.
* `dynamic_projection_eq_limitHom χ T` identifies the projection with the
  published limit homomorphism `Dynamic.limitHom χ T` (CGP Lemma 2.1.5). By
  `projection_eq_iff` it suffices that `(lim p)⁻¹ p ∈ U(χ)(T)`. This is the
  conjugate of the published `p (lim p)⁻¹ ∈ U(χ)(T)` by `(lim p)⁻¹ ∈ P(χ)(T)`.

## Rational points

The rational points are the case `S = Spec F` and `T = Over.mk (𝟙 (Spec F))`,
the identity test object. This is the convention `G(k) := Over.mk (𝟙 _) ⟶ G.X`
of the algebraic-groups program, so `dynamic_isSemidirectDecomposition χ
(Over.mk (𝟙 _))` is `P(χ)(F) = Z(χ)(F) ⋉ U(χ)(F)`.

This module fixes no topology on `G(F)`. To apply the functors of
`Aubert.General.Parabolic`, a consumer binds the point topology of the Conrad
point-topology task `886bf565`. That is `PointTopology.rationalPointTopology`
on the identity-test carrier, from candidate `5ea5f6f1`, which is not public at
Library `0ebc0efd`. The consumer then supplies
`[LocallyCompactSpace]` and `[NonarchimedeanGroup]` for it, together with
closedness of `U(χ)(F)`. For a nonarchimedean local field these properties are
external structural inputs (Renard V.2.1; Conrad, Proposition 2.1), and nothing
here proves them. Statements must use that pinned topology rather than an
arbitrary one: with an arbitrary topology, for example the discrete one, the
representation-theoretic targets are false.

The construction needs neither connectedness nor reductivity of `G`. For
`IsConnectedReductive G`, the field `isAffineHom` gives separatedness by
`IsSeparated.of_isAffineHom`.

## Sources

* B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, §2.1 (dynamic
  method), as cited by the published `Dynamic` modules.
* D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version),
  registered as `renard-2026-representations-groupes-reductifs-padiques`: V.2.1
  (topology of `G(F)`, for the scope above) and V.3.1 (Levi decomposition
  `P = M ⋉ N`, which `dynamic_isSemidirectDecomposition` realizes for dynamic
  parabolics).
