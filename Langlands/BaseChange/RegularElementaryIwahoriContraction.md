# Iwahori contraction data for the regular elementary double coset

The module `Langlands.BaseChange.RegularElementaryIwahoriContraction` supplies
the group-theoretic and measure-theoretic inputs for the regular elementary
trace formula on `GL_{r+1}(E)`. Here `E` is a canonical p-adic field with residue
cardinality `q`, `I = regularElementaryCompactOpenSubgroup E r` is the compact
open subgroup of `GL_{r+1}(O_E)` with diagonal reduction, `B = singletons (r+1)`
is the Borel shape, and `N`, `M`, `Nbar` are its upper unipotent, diagonal and
lower unipotent subgroups. The element `t = torus π ν = diag(π^{ν_i})` has `π` of
order one and `ν` strictly decreasing.

## The Haar modulus of a Levi element

`closedNormalizerCharacter_unipotentSubgroup_eq_leviModulus` holds for every
p-adic field with a supplied realization `T`, every rank and every block shape
`C`. For a normalizer element `g` of the ambient upper radical with
`g = C.leviEmbedding l`, it states

`HaarModulus.closedNormalizerCharacter (C.unipotentSubgroup F) _ g = T.leviModulus C l`.

The proof follows the published `Geometric.parabolicOrbitStagesRadicalModulus`.
The topological group isomorphism `C.unipotentRadicalAmbientEquiv` carries
conjugation by `C.leviInParabolic l` on the radical in the parabolic to
conjugation by `g` on the ambient radical. `Geometric.haarChar_eq_of_conjugacy`
then identifies the two Haar characters. The published `glBlockModulusHaar`
says that conjugation scales Haar measure on the parabolic radical by
`(T.leviModulus C l)⁻¹`.

## The contraction conditions

- `normalizedAbs_zpow_of_ord_eq_one`: `|π^k| = q^{-k}`, from
  `normalizedAbs_of_ne_zero` and `ord_zpow`.
- `isStrictlyContracting_weightPowers`: the tuple `(π^{ν_i})` is strictly
  contracting for `B`. Each forward ratio has absolute value `q^{ν_j - ν_i} < 1`
  for `i < j`.
- `torus_mem_leviSubgroup`: `t` lies in the diagonal Levi.
- `regularElementary_isIwahoriContraction`: `Jacquet.IsIwahoriContraction I N M Nbar t`.
  The proof uses the published filtration
  `regularElementaryStrictFiltration E 1 π hπ ν hν`, taken with the identity
  automorphism.
  - Its level-zero factorization gives the Iwahori factorization of `I`.
  - Its upper and lower steps, together with `M` normalizing `N` and `Nbar`,
    give the `upper` and `lower` conditions. The `levi` condition holds because
    diagonal matrices commute.
  - Iterating the lower step puts `t^{-s} l t^s` in level `s`, and cofinality of
    the filtration gives the uniform `contract` condition.
  - The `exhaust` condition is the published
    `GeneralLinear.BlockShape.strictPowers_eventually_mem_iwahori` for the
    strictly contracting tuple, rewritten with `GeneralLinear.torus_eq_blockScalar`.

## The index and the measure

- `iwahoriIndex_regularElementary`: `[I ∩ N : t (I ∩ N) t⁻¹] = q^{ρ(ν)}` with
  `ρ(ν) = regularElementaryRho ν`.
  - The published `Jacquet.closedNormalizerCharacter_mul_iwahoriIndex` gives
    `δ_N(t) · [I ∩ N : t (I ∩ N) t⁻¹] = 1`.
  - By the modulus theorem above, `δ_N(t)` is the block modulus of
    `blockScalarLevi (π^{ν_i})`.
  - The published `ProductLeviNecessity.leviModulus_blockScalarLevi_of_abs`
    evaluates it as `q^{-ρ(ν)}`, since all block sizes are one.
- `natCard_quotient_regularElementaryConjIntersection`: the number of cosets of
  `I ∩ t I t⁻¹` in `I` is `q^{ρ(ν)}`. This combines the previous result with
  `natCard_quotient_conjIntersectionSubgroup` of the module
  `Langlands.BaseChange.DoubleCosetTwistedTrace`.
- `card_regularElementaryCosets_mul_measure`: `[K : I] · μ(I) = 1`, that is
  `μ(I) = [K : I]⁻¹`, where `K = GL_{r+1}(O_E)` and `μ = sphericalHaar E r` is
  the Haar measure on `GL_{r+1}(E)` normalized by `μ(K) = 1`. The ambient
  measure has infinite total mass; only its restriction to `K` is a probability
  measure. The result follows from the published `Jacquet.relIndex_mul_measure`
  and `RankinSelberg.normalizedCompactOpenHaar_self`.

## Provenance

These are derived inputs to a compression proof of Henniart–Lemaire,
*Changement de base et induction automorphe pour GLₙ en caractéristique non
nulle*, Mém. SMF 124 (2011), I.5.3, Proposition, printed pp. 31–32 (PDF
pp. 39–40). In the printed proof the factor `q^{ρ(lν)}` is the Jacobian `J(t)`
of an orbital chart. Here the same number `q_E^{ρ(ν)}` appears as the index
`[I : I ∩ t I t⁻¹]`, which is the inverse of the Borel modulus at `t`.
Registered literature ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
