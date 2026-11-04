# Forward transport and factorization of the original epsilon corrections

This internal deduction by Worker 184 is a normalization prerequisite for the
rational geometric lemma. It uses the original Haar corrections, conjugation
invariance of actual Haar characters, and the proved correction-intersection
semidirect decomposition. It makes no new literature translation claim.

For subgroups `MI`, `MJ` of a locally compact topological group `A`, and any
`n : A`, put `L = MI ∩ n MJ n⁻¹`. Every character in this module has the literal
nested domain `Lt = L.subgroupOf MI`. The map `flat` is the canonical
`Subgroup.subgroupOfEquivOfLe inf_le_left`, regarded as a homomorphism from
`Lt` to `L`; its ambient point is unchanged.

`geometricCommonLeviIntersectionModulus MI MJ n U V` is the actual closed
Haar character on `U ∩ n V n⁻¹`, restricted to `L` and pulled back along
`flat`. Closedness of `U` and `V`, normalization of `U` by `MI`, and
normalization of `V` by `MJ` are explicit inputs. The imported
`geometricCommonLevi_normalizes_intersection` derives normalization by `L`.
`geometricForwardSourceRadicalModulus` instead uses the whole forward
conjugate `n UJ n⁻¹`. It assumes `UJ` closed and normalized by `MJ`;
normalization by `L` follows by mapping that normalizer containment and using
`L ≤ n MJ n⁻¹`. Both definitions use the existing
`HaarModulus.closedRestrictCharacter`, with its forward conjugation convention,
and take values in the positive nonnegative-real units.

The three ambient transport theorems preserve these literal groups and points:

- `geometricSourceCorrectionRadicalModulus_eq_forward` identifies the original
  source-radical character, evaluated at `n⁻¹ x n`, with forward conjugation
  on `n UJ n⁻¹` at `x`.
- `geometricSourceCorrectionIntersectionModulus_eq_forward` identifies the
  original source correction subgroup
  `{u ∈ UJ | n u n⁻¹ ∈ PI}`, acted on at `n⁻¹ x n`, with
  `PI ∩ n UJ n⁻¹`, acted on at `x`. It retains closedness of both `PI` and
  `UJ`, and their normalization by the two original Levi groups.
- `geometricTargetCorrectionIntersectionModulus_eq_forward` identifies the
  original target correction subgroup for `(MI, MJ, UI, PJ, n⁻¹)` with
  `UI ∩ n PJ n⁻¹` at the same ambient point. It retains the analogous
  closedness and normalizer inputs for `UI` and `PJ`.

The source proofs apply `closedNormalizerCharacter_conj` to the actual
normalizer points. The original transported point is proved equal to
`n⁻¹ x n` using `geometricSourceCorrectionTransport_apply`; equality of the
normalizer subtypes then identifies the values. The correction-subgroup
membership equivalence follows from `mem_geometricTargetIntersection`,
`Geometric.General.mem_correctionSubgroup`, and group cancellation. The
target proof specializes
`geometricTargetCorrectionIntersectionModulus_eq_ambient` with the
point-preserving normalizer inclusion. These ambient theorems require no
reductivity, finite length, or second countability.

The rational specialization works over any field `k : Type u`, with an affine
ambient group scheme, the actual maximal split torus `i`, the actual generic
cocharacter `ν`, connected reductivity, `StandardCocharacterStatement` and
`HasPointNormalizerComparison`. It retains any `I`, `J`, the two original
standard semidirect decompositions `dI`, `dJ`, and any actual normalizer point
`n`; no minimal-representative premise occurs. The rational-point topology may
be any locally compact, second countable topological group topology. The
closedness inputs are the original `PI`, `MI`, `UI`, and `UJ`, and continuity
is assumed only for the original `dI.projection`. No characteristic-zero,
splitness or positive-rank condition is added.

Write `V = n UJ n⁻¹`, `B = MI ∩ n UJ n⁻¹`, and
`C = UI ∩ n UJ n⁻¹`. Here `B` is the literal target endpoint radical and `C`
is the common unipotent intersection. Let `δV` be
`geometricForwardSourceRadicalModulus`, and let `δB`, `δC` be the respective
`geometricCommonLeviIntersectionModulus` characters, all on `Lt`.
`geometricEpsilonOne_correctionModulus_eq_mul` proves that the original
transported source correction-subgroup modulus equals `δB * δC`.
The proof first uses the source transport theorem above, then pulls back
`geometricCorrectionIntersection_modulus_eq_mul` along `flat`. That imported
result constructs

`PI ∩ n UJ n⁻¹ = (MI ∩ n UJ n⁻¹) ⋉ (UI ∩ n UJ n⁻¹)`

from preservation by the original Levi projection and applies the continuous
semidirect Haar product theorem. Neither this decomposition nor its Haar
identity is a new assumption here.

Finally `geometricEpsilonOne_eq_factorized_half` proves the exact equality of
complex-unit-valued characters on every point of `Lt`:

`geometricEpsilonOne = complexCharacter (positiveHalfCharacter δV) * inverseHalfCharacter δB * inverseHalfCharacter δC`.

It unfolds the original `geometricEpsilonOne`, uses
`geometricSourceCorrectionCharacter_eq`, replaces the original radical by its
forward transport, and uses the preceding correction-modulus product.
Multiplicativity of the canonical square-root homomorphism and complex-unit
embedding distributes the inverse half over that product. Thus no choice of
square-root sign and no freely supplied scalar character enters the formula.
The theorem proves this factorization on the entire literal common Levi; it
does not extend the distinct five-subgroup root-weight balance from torus
points to that Levi.

The proof bodies directly use subgroup transport, conjugation invariance of
Haar modulus, the actual correction-intersection Haar product and the
canonical half-character definitions. They use no geometric-lemma expansion,
orbit-functor comparison, adjointness, cuspidal support, character independence
or Langlands classification theorem. The imported `Conjugation` module also
contains normalized representation and exact-K0 comparisons, while
`RationalGeometricCorrections` imports compact-integral constructions; those
additional declarations are not invoked here. This identifies direct uses
without asserting a fresh semantic audit of the entire imported closure.
Whole-Levi distinct-radical balance, fully normalized coefficient comparison,
compact/full induction comparison, the ordered orbit filtration and the host
exact-K0 expansion remain separate obligations.
