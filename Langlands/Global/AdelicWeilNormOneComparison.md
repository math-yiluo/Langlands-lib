# Canonical norm-one adelic comparison for Weil restriction

Author: Worker 82.

For every extension `L/F` of number fields in universe `u` and every affine
group scheme `G` locally of finite type over `L`, this module constructs the
canonical multiplicative equivalence

`adelicPointsEquiv F L G : (Res_{L/F} G)(𝔸_F) ≃* G(𝔸_L)`.

It uses the published actual group scheme `AffineWeil.groupScheme F L G`,
its equivalence with tensor-valued points, and the proved canonical full
adelic tensor isomorphism `numberFieldAdeleTensorEquiv F L`.
`adelicPointsEquiv_apply` records its exact coefficient map:
`numberFieldAdeleTensorMap F L`, which sends `a ⊗ x` to `a · inclusion(x)`.
No choice of an arbitrary equivalence replaces this map. The rational
comparison `rationalPointsEquiv` is the published
`AffineWeil.basePointsEquiv`, including the canonical tensor-unit map.

`tensorMap_comp_principal` proves the exact coefficient square: tensoring
the diagonal map `F → A_F` with `L` and then applying the canonical adelic
tensor map equals tensor-unit `L ⊗[F] F → L` followed by the diagonal
map `L → A_L`. The proof checks pure tensors using the published
`adeleInclusion_diagonal` and extends by addition.
`adelicPointsEquiv_rational` combines this identity with the existing
all-algebra naturality of `AffineWeil.pointsEquiv`. It proves that every
principal point maps to the principal point of `rationalPointsEquiv`,
without a topological or character-norm premise.

`NormOneComparisonStatement` is an unproved proposition target containing
three assertions about these fixed maps:

- The canonical adelic equivalence is a homeomorphism for the Library's
  existing regular-function evaluation topologies.
- It sends every principal point to the principal point of its specified
  rational comparison, as proved by `adelicPointsEquiv_rational`.
- It maps the actual `normOneSubgroup F (Res G)` onto
  `normOneSubgroup L G`, each defined by the normalized idelic norm of every
  rational algebraic character over its own base field.

The statement imposes no reductivity, connectedness, splitting, compactness,
or supplied topological comparison. Finite-dimensionality and separability
of the number-field extension follow from the field assumptions. The
module does not prove the remaining topology and norm-one image assertions,
quotient compactness, or
Springer's central-maximal-split compactness theorem. In particular, the
algebraic equivalence alone does not assert a topological or character-norm
comparison.

This is a derived number-field specialization of T. A. Springer,
*Reduction theory over global fields* (1994), §1.4, printed pp.208–209
(PDF pp.2–3), and §3.1(a)–(b), printed p.214 (PDF p.8).
Those passages identify actual rational and adelic points under restriction
of scalars and identify the norm-one subgroups. The registered source is
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`, file
`literature/Reduction theory over global fields (Springer, 1994).pdf`.
No errata note exists for this source.
