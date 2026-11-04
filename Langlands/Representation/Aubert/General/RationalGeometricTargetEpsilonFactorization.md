# Factorization of the original rational target epsilon

This internal deduction by Worker 184 completes the target counterpart of
`RationalGeometricEpsilonFactorization`. It uses the actual standard radical
intersection product, the original inducing-side semidirect decomposition,
forward conjugation, and the actual continuous semidirect Haar product.
It makes no new literature translation claim.

The results retain an arbitrary field `k : Type u`, an affine ambient group
scheme `G`, its actual maximal split torus `i`, the generic cocharacter `ν`,
connected reductivity, `StandardCocharacterStatement`, and
`HasPointNormalizerComparison`. The two standard indices `I`, `J` and the
actual torus-normalizer point `n` are arbitrary. There is no minimality,
characteristic-zero, splitness, or positive-rank condition. The topology on
the rational points may be any topological-group topology.

Write `H = G(k)` and let `PI`, `MI`, `UI`, `PJ`, `MJ`, `UJ` denote the
original standard rational-point subgroups. Put

`Q = n PJ n⁻¹`, `N = n MJ n⁻¹`, `V = n UJ n⁻¹`,

`L = MI ∩ N`, `D = UI ∩ Q`, `A₀ = UI ∩ N`, `C = UI ∩ V`.

Every displayed conjugate is the literal subgroup image under
`MulAut.conj n`, and every intersection is the literal
`geometricTargetIntersection` in `H`. Here `A₀` is the source endpoint
radical transported forward to the target ambient group; no ambient point
is altered in its action by `L`.

`geometricTargetCorrectionIntersectionDecomposition` proves

`IsSemidirectDecomposition D A₀ C`.

It uses the existing `geometricUnipotentParabolic_eq_mul`, which proves
`D = A₀ C` by the actual standard-cocharacter and common-torus intersection
theorems. It applies `RefinedIntersection.innerDecomposition` to that
identity and the forward conjugate of the original `dJ`. The generic
construction derives the containment and normalizer conditions from these
literal intersections, and derives uniqueness from the original
semidirect decomposition. Thus neither an intersection product nor its
decomposition is supplied as a new premise.

`continuous_geometricTargetCorrectionIntersection_projection` obtains
continuity of this projection from continuity of the original
`dJ.projection`. It applies
`RefinedIntersection.continuous_inner_projection` to the forward-conjugate
decomposition, whose projection continuity follows from
`dJ.continuous_forwardConjugate_projection`. The generic subdecomposition
projection has the same ambient value as the restriction of that conjugated
original projection.

`geometricTargetCorrectionIntersectionCoordinates` is the resulting
homeomorphism `A₀ × C ≃ₜ D`. Its apply theorem gives the exact forward
value `a * c` in `H`. These decomposition and coordinate results require
neither local compactness nor closedness.

The Haar results additionally assume local compactness and second
countability of `H`, both original decompositions `dI`, `dJ`, and
closedness of `UI`, `PJ`, `MJ`, `UJ`. Forward conjugation preserves the
last three closed subgroups. The original Levi containments and
`levi_le_normalizer` derive the action of `L` on `D`, `A₀` and `C` by
`geometricCommonLevi_normalizes_intersection`.
`geometricTargetCorrectionIntersection_modulus_eq_mul` proves equality of
actual positive-unit-valued characters on all of `L`:

`δD = δA₀ * δC`.

Here each character is `HaarModulus.closedRestrictCharacter` for the
indicated literal subgroup, acting by forward conjugation at the original
ambient common-Levi point. The proof evaluates at an arbitrary `l : L`
and applies the continuous semidirect
`closedNormalizerCharacter_eq_mul` theorem to the constructed decomposition.
The closedness and continuity needed by that theorem are derived above.
No determinant or root-weight identity is used.

The original target epsilon is defined on the nested subgroup
`Lt = L.subgroupOf MI`. Let `δA₀` and `δC` now denote the existing
`geometricCommonLeviIntersectionModulus` characters on `Lt`, obtained by
pulling back the preceding characters along the canonical
`Subgroup.subgroupOfEquivOfLe inf_le_left`. This map preserves the ambient
point. `geometricEpsilonTwo_correctionModulus_eq_mul` identifies the
original `geometricTargetCorrectionIntersectionModulus` with
`δA₀ * δC`. Its proof first uses the previously proved
`geometricTargetCorrectionIntersectionModulus_eq_forward`, then evaluates
the Haar product at that canonical image of `l : Lt`. In particular, the
original target correction for `(MI, MJ, UI, PJ, n⁻¹)` acts on
`UI ∩ n PJ n⁻¹` at `l`, with no inverse of the Haar convention.

Finally let `δU` be the original
`geometricTargetCorrectionRadicalModulus` on `Lt`, the forward Haar
character of `UI` at the same ambient point. The theorem
`geometricEpsilonTwo_eq_factorized_half` proves the exact character equality

`geometricEpsilonTwo = complexCharacter (positiveHalfCharacter δU) * inverseHalfCharacter δA₀ * inverseHalfCharacter δC`.

It unfolds the existing target epsilon, uses
`geometricTargetCorrectionCharacter_eq`, replaces its correction modulus
by the proved product, and distributes the canonical square-root
homomorphism, complex-unit embedding and inversion over that product.
Thus the two intersection factors occur with their canonical inverse
halves, and no freely supplied scalar correction or square-root sign is
introduced. Continuity is assumed only for `dJ.projection` in this target
formula, while the source formula in the imported epsilon module uses the
original `dI.projection`.

All three Haar identities hold on every point of their displayed common
Levi, rather than only after restriction to the torus image. They concern
factorization of one correction subgroup, and do not extend the separate
five-subgroup distinct-radical balance from the torus to the whole Levi.
The direct proof uses the actual subgroup product and semidirect Haar
product, then canonical half-character algebra. The imported modules also
contain further normalized and compact-integral constructions; this
description does not assert a fresh semantic audit of their full closure.
Whole-Levi distinct-radical balance, normalized representation comparison,
compact/full induction comparison, the ordered filtration and the host
exact-K0 expansion remain separate obligations.
