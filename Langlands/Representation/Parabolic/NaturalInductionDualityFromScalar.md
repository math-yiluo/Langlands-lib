# Natural induction duality from the GL scalar compact integral

Author: Worker 715.

This module proves that the published scalar compact-picture integral for
standard GL parabolics, `Langlands.GLParabolicCompactScalarIntegralStatement`,
implies the published target
`Langlands.Parabolic.NaturalNormalizedInductionDualityStatement`. That target
covers both `StandardNaturalInductionDualityClause` and
`RefinedNaturalInductionDualityClause`. The scalar statement enters only as the
explicit hypothesis `hGL` of each theorem. This module does not prove it.

The route is Casselman's Proposition III.1.1. The source is
`casselman-2019-jacquet-module`, Chapter III, revision April 29, 2019,
section 1, pages 1–2. The general argument is in
`Langlands.Representation.Induction.CompactPairingDuality`. This module
supplies the actual groups, characters, compact subgroups and measures.

## Results

- `generalLinear_zero_subsingleton`. `GeneralLinear 0 R` is trivial.
- `exists_compactScalarData`. Fix a realization `T` and a block shape `B` of any
  rank `n`, with `0` allowed. The result gives a compact subgroup `K` of
  `GL_n(F)` and a probability measure `μ` on its Borel space that charges every
  nonempty open set. For every locally constant `φ` covariant by the full Levi
  modulus `T.leviModulus B (B.leviProjection q)`, and every `g`, the function
  `k ↦ φ(k g)` is integrable and its integral equals that of `φ`.
  - In positive rank this is the conclusion of `hGL`. A Haar measure is
    open-positive.
  - In rank zero the group is trivial. The proof takes `K = ⊤` and the Dirac
    mass at `1`, and every identity is immediate. The scalar statement assumes
    `0 < n`, so this case is handled here.
- `standardNaturalInductionDuality_of_scalar`. For each `p`, `F`, `T`, `n` and
  `B`, apply `Induction.exists_integralDualEquiv` with the following data:
  - `P = B.parabolic F.Carrier` and `m = B.leviProjection F.Carrier`, which is
    continuous by `T.blockLeviProjection`.
  - `χ = T.parabolicHalfModulus B`, whose kernel is open by
    `T.isOpen_ker_parabolicHalfModulus`.
  - `δ q = T.leviModulus B (m q)`. The identity `χ q * χ q = δ q` comes from
    `T.leviHalfModulus_sq`.
  - The compact data above.

  Cofinal compact open subgroups of the Levi come from
  `T.leviNonarchimedean`, `T.leviLocallyCompactSpace` and
  `compactOpenSubgroupBasis`. Admissibility of the induced representation is
  the Library's `Parabolic.normalizedInductionAdmissibility`. The family is
  `E σ hσ := Classical.choose` of the resulting existence statement, which
  fixes one equivalence per admissible `σ`. Its integral characterization
  holds for the same `K` and `μ`, chosen once per `(T, B)`. Naturality on an
  intertwiner `a` is `Induction.integralDualEquiv_natural` with
  `A = B.inducingMap _ a` and `A' = B.inducingMap _ (contragredientMap a)`. The
  pairings are adjoint by definition (`rfl`).
- `refinedLevi_compactOpenCofinal`. The actual refined Levi
  `refinedLevi F.Carrier B S` has arbitrarily small compact open subgroups. It
  is nonarchimedean and locally compact because it is topologically isomorphic
  to the Levi of `B.flatten S`, by `flattenedLeviEquivContinuous`.
- `refinedLeviModulus_mulSingle`. Take a refined parabolic element whose
  underlying element of `B.Levi` is `Pi.mulSingle j q`, with
  `q ∈ (S j).parabolic`. Its refined Levi modulus is
  `T.leviModulus (S j) ((S j).leviProjection q)`. The proof uses
  `refinedLeviModulus_apply`, `refinedLeviBlock_projection`, and the vanishing
  of the other factors.
- `refinedNaturalInductionDuality_of_scalar`. The ambient group is
  `B.Levi F.Carrier = ∀ i, GL_{B.size i}(F)`, with the following data:
  - `P = refinedParabolic F.Carrier B S` and `m = refinedLeviProjection`, which
    is continuous.
  - `χ = T.refinedParabolicHalfModulus B S`, with open kernel.
  - `δ q = T.refinedLeviModulus B S (m q)`. The identity `χ q * χ q = δ q`
    comes from `T.refinedLeviHalfModulus_sq`.

  For each block `i`, `exists_compactScalarData` applied to `S i` gives
  `K i ≤ GL_{B.size i}(F)` and `μ i`. Each `K i` is second countable as a
  subspace of the second countable `GL_{B.size i}(F)`. The compact subgroup is
  `Subgroup.pi Set.univ K` with `Induction.piSubgroupMeasure K μ`. The scalar
  hypothesis for the product follows from `Induction.piSubgroup_scalarIntegral`
  with factor weights `T.leviModulus (S i) ∘ (S i).leviProjection`, matched by
  `refinedLeviModulus_mulSingle`. Admissibility is the Library's
  `Parabolic.normalizedRefinedInductionAdmissibility`. Naturality uses
  `refinedInducingMap B S (T.refinedLeviHalfModulus B S)` on `a` and on
  `contragredientMap a`. The refined input `σ` is an arbitrary representation
  of the whole refined Levi, with no tensor factorization.
- `naturalNormalizedInductionDuality_of_scalar` pairs the two clauses.

## Scope

Every quantifier of the target is preserved: field and carrier universes, prime,
realization, rank (including `0`), block shape and refinement. No pointwise
duality, finite length or irreducibility is assumed. The only extra hypothesis
is `hGL`, the published scalar statement. This module states only the
reduction. `Langlands.Representation.Parabolic.NaturalInductionDualityProof`
discharges `hGL` with the Library theorem
`Langlands.glParabolicCompactScalarIntegral`.
