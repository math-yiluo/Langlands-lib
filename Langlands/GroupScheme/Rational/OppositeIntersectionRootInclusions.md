# Opposite-radical intersections inside a dominant dynamic radical

Lean module: `Langlands.GroupScheme.Rational.OppositeIntersectionRootInclusions`,
namespace `Langlands.GroupScheme`.

## Purpose and provenance

Provenance: internal. In the convergence proof of the standard intertwining integrals
(Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*
(2003), IV.1.1, printed pp. 277–281), a point of `Ū ∩ U'`, the intersection of the radical
opposite to one parabolic `P` with the radical of a second parabolic `P'` sharing a Levi, is
controlled by modulus characters of auxiliary parabolics. This module supplies the structural
input for that estimate. For every cocharacter `mu` that is nonnegative on the roots of
`Ū ∩ U'`, it finds a single dynamic radical `U(n • mu - zeta)` that contains `Ū ∩ U'` and whose
parabolic lies in `P(mu)`. The statements and arguments are derived from Library results and are
not transcribed from the source, which argues with roots of a reductive group.

## Setting and notation

- `k` is a field, `G` is a group scheme over `Spec k` with affine structure map, `T` is a
  commutative group scheme over `Spec k`, and `i : T.toGrp ⟶ G` is an arbitrary homomorphism.
  Where stated, `T` is a split torus (`IsSplitTorus T.toGrp`).
- For `c : cocharacterLattice T`, the cocharacter of `G` is `CommGroupScheme.groupHom c ≫ i`.
  `P(c)`, `U(c)` and `Z(c)` denote the dynamic parabolic, dynamic unipotent subgroup and dynamic
  centralizer of that cocharacter (`Dynamic.parabolic`, `Dynamic.unipotent`,
  `Dynamic.centralizer`), as subgroup functors on all test schemes. Thus `U(-zeta)` is the
  radical opposite to `P(zeta)`.
- `relativeRoots i` is the set of actual relative roots of `i` (nonzero characters of `T` with
  nonzero weight space in the Lie algebra of `G`), and `latticePairing T α c` is the integer
  pairing `⟨α, c⟩`.
- In the intended application `zeta` and `eta` are the split-component cocharacters of the two
  parabolics `P` and `P'`. Then `U(-zeta) ⊓ U(eta)` is `Ū ∩ U'`, and `Z(eta) ≤ Z(zeta)` holds
  because the Levis agree.

## Declarations

- `IsOppositeIntersectionAdmissible i zeta eta mu` (definition): for every
  `α ∈ relativeRoots i`, `⟨α, zeta⟩ < 0` and `0 < ⟨α, eta⟩` imply `0 ≤ ⟨α, mu⟩`. In words,
  `mu` is nonnegative on every actual root that is negative on `zeta` and positive on `eta`. It
  only requires `G` to have affine structure map.
- `relativeRoot_pairing_eq_zero_of_centralizer_le`: assume `T` is split, `G` is affine and locally
  of finite type, and `Z(eta) ≤ Z(zeta)`. If `α ∈ relativeRoots i` and `⟨α, eta⟩ = 0`, then
  `⟨α, zeta⟩ = 0`.
- `unipotent_neg_inf_unipotent_le`: assume `T` is split, `G` is smooth and affine,
  `Z(eta) ≤ Z(zeta)`, and `0 < ⟨α, theta⟩` for every `α ∈ relativeRoots i` with
  `⟨α, zeta⟩ < 0` and `0 < ⟨α, eta⟩`. Then `U(-zeta) ⊓ U(eta) ≤ U(theta)` as subgroup functors.
- `exists_dominant_nsmul_sub`: assume `G` is affine and locally of finite type. For any `zeta`
  and `mu` there is `N` such that for all natural `n ≥ N`, `P(n • mu - zeta) ≤ P(mu)`,
  `U(mu) ≤ U(n • mu - zeta)` and `Z(n • mu - zeta) ≤ Z(mu)`. No split or root hypothesis is
  needed.
- `exists_unipotent_inf_le_and_parabolic_le` (main result): assume `T` is split, `G` is smooth
  and affine, `Z(eta) ≤ Z(zeta)` and `IsOppositeIntersectionAdmissible i zeta eta mu`. Then there
  is `N` such that for all natural `n ≥ N`, `U(-zeta) ⊓ U(eta) ≤ U(n • mu - zeta)` together with
  the three inclusions of `exists_dominant_nsmul_sub`.

## Proofs

- `relativeRoot_pairing_eq_zero_of_centralizer_le`: by the public
  `weightSpace_inf_tangentSubmodule_centralizer`, the weight space of `α` meets the tangent
  submodule of `Z(c)` in the whole weight space if `⟨α, c⟩ = 0` and in `⊥` otherwise. Since
  `⟨α, eta⟩ = 0`, the weight space lies in the tangent submodule of `Z(eta)`. Monotonicity of
  tangent submodules (`RelativeRoot.tangentSubmodule_mono`) puts it in the tangent submodule of
  `Z(zeta)`. If `⟨α, zeta⟩ ≠ 0`, this intersection is `⊥`, so the weight space is `⊥`. That
  contradicts `α` being an actual root.
- `unipotent_neg_inf_unipotent_le`: work in the ambient group `H = P(eta)`, represented by the
  public affine closed representative `Dynamic.Affine.parabolicHom`. `H` is smooth by the proved
  `dynamicSmooth`. The torus factors through `H` because its image centralizes `eta`, giving
  `iH : T ⟶ H`. Dynamic unipotent subgroups and parabolics of `H` are the comaps of those of `G`
  (`Dynamic.unipotent_eq_comap_of_isClosedSubgroup`, `Dynamic.parabolic_eq_comap_of_isClosedSubgroup`),
  so `P(eta)` is all of `H`. The public `RelativeRoot.nonnegative_rootSupport_of_parabolic_le`,
  applied to `0` and `eta` in `H`, then makes every root of `iH` nonnegative on `eta`. Each root
  of `iH` is a root of `i` (`relativeRoots_subset_of_factor`). A root of `iH` that is positive on
  `-zeta` cannot be orthogonal to `eta`, by the previous lemma, so it is positive on `eta` and the
  hypothesis on `theta` applies. The proved smooth root-sign radical criterion
  `rootSignUnipotentInclusions`, applied in `H`, gives `U_H(-zeta) ≤ U_H(theta)`. A point of
  `U(-zeta) ⊓ U(eta)` lies in `P(eta)`, so it comes from a point of `H`, and the comap
  identities carry the inclusion back to `G`.
- `exists_dominant_nsmul_sub`: apply the public `Dynamic.exists_dominant_inclusions` to the
  commuting cocharacters `mu` and `-zeta` (the range of the second centralizes the first because
  both factor through `T`). The pointwise identity
  `t ↦ (n • mu - zeta)(t) = mu(t)^n · (-zeta)(t)` follows from additivity of
  `CommGroupScheme.groupHom`.
- `exists_unipotent_inf_le_and_parabolic_le`: the dominance lemma gives `N` and the last three
  inclusions. For `α` negative on `zeta` and positive on `eta`, admissibility gives
  `⟨α, n • mu - zeta⟩ = n⟨α, mu⟩ - ⟨α, zeta⟩ > 0`, so `unipotent_neg_inf_unipotent_le` with
  `theta = n • mu - zeta` gives the first inclusion.

No reductivity, connectedness, characteristic, reduced-root-system or neg-closure of the root set
is assumed.
