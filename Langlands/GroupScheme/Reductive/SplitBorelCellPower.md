# Saturation of realized weights of a split pinning

This is an internal supporting module for the proof of
`SplitDominantHighestWeightRepresentationsExistStatement`. It builds on
`Langlands.GroupScheme.Reductive.SplitBorelCell`, which fixes for
`p : SplitPinning G` the negative Borel subgroup `p.negativeBorel = P_G(ν⁻¹)`, the
positive unipotent subgroup `p.positiveUnipotent = U_G(ν)`, a big-cell coordinate
`p.cellCoordinate`, and the predicates `p.IsRealizedBy lam f` and
`p.IsRealizedWeight lam`. A coordinate `f` realizes `lam` when it is left
covariant for `p.negativeBorel` with the extended character of `lam`, right
invariant under `p.positiveUnipotent`, and has counit one.

The main result is saturation over an algebraically closed field
(`IsRealizedWeight.of_nsmul`): if `n • lam` is realized for some `n > 0`, then so
is `lam`. It is a step of this project's route to dominant highest-weight
existence: positive multiples of dominant weights are realized by
`DominantMultipleAssembly`, and saturation then realizes the weight itself. The
proof is direct. A realizing coordinate for `n • lam`
is an `n`-th power on the big cell. Normality of the coordinate ring of `G` makes
the root a regular function. Covariance and invariance of the root then follow
from `CovariantPowerDescent`. No declaration formalizes a literature statement.

Throughout, `k : Type u` is a field, `G` is a group scheme over
`Spec (CommRingCat.of k)` with `[IsAffineHom G.X.hom]`, and `p : SplitPinning G`.
`algebra G` denotes `AffineCoordinates.algebra G`.

## Values on the big cell

`pointAlgebraHom_borelCharacterCoordinate_nsmul`: at every point of
`p.negativeBorel`, the extended character coordinate of `n • lam` takes the
`n`-th power of the value of that of `lam`. The proof is by induction from
`pointAlgebraHom_borelCharacterCoordinate_add` and `_zero`.

`IsRealizedBy.pointAlgebraHom_cell`: if `f` realizes `lam`, then at a cell point
`(a ≫ p.negativeBorelHom) * (u ≫ p.positiveUnipotentHom)` the value of `f` is
the value of the extended character coordinate of `lam` at `a`. This uses right
invariance first, then left covariance at `(a, 1)` together with counit one.

`bijective_algSpecCounit`: for a commutative `k`-algebra `B`, the counit
`Γ(Spec B) → B` of the `algΓ ⊣ algSpec` adjunction is bijective, since `algSpec`
is fully faithful.

`IsRealizedBy.exists_pow_eq_algebraMap`: if `F` realizes `n • lam`, then there is
`x : Localization.Away p.cellCoordinate` with `x ^ n = algebraMap F`.

Proof. Let `g` be the tautological point of `G` with values in
`Localization.Away p.cellCoordinate` (`AffineCoordinates.algPoint`). The cell
coordinate is a unit at `g`, so `g` factors through the big cell
(`exists_factors_of_isUnit_cellCoordinate`) as `(a ≫ i) * (u ≫ j)`. Take `x` to
be the element corresponding, under the bijective counit, to the value at `a` of
the extended character coordinate of `lam`. Then `x ^ n` corresponds to the value
of the coordinate of `n • lam` at `a`, which by `pointAlgebraHom_cell` is the
value of `F` at `g`, that is, `algebraMap F`.

## Normality and domains

`isDomain_algebra_of_smooth`: if `H` is smooth over `k` with connected underlying
space, then `algebra H` is a domain. `H.X.left` is integral
(`CharacterLatticeProof.isIntegral_of_smooth`), and
`AutomorphicAction.coordinate_isDomain` applies.

`isDomain_tensor_algebra_of_smooth`: over an algebraically closed field, for
such `H` and any `k`-algebra domain `B`, the tensor product `algebra H ⊗[k] B`
is a domain. Here `algebra H` is of finite type (`AffineCoordinates.algebraFiniteType`),
and the Library's
`GeomIntegralOfIsAlgClosed.isDomain_tensorProduct_of_isAlgClosed` applies.

`isIntegrallyClosed_algebra_of_isConnectedReductive`: if `G` is connected
reductive, then `algebra G` is integrally closed. It is a domain
(`isDomain_of_isConnectedReductive`) and smooth over `k`
(`AffineCoordinates.smooth_algebra`). Its localizations at primes are integrally
closed (`SmoothIntegralNormalStalks.integrallyClosed_localization_of_smooth_domain`),
and `IsIntegrallyClosed.of_localization_maximal` concludes.

`smooth_negativeBorel` and `connectedSpace_negativeBorel`: the negative Borel
subgroup is smooth (`dynamicSmooth`) with connected underlying space
(`DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic`), because `G` is
smooth with connected underlying space.

`isDomain_negativeBorel_tensor` and `isDomain_positiveUnipotent_tensor`: over an
algebraically closed field, `algebra p.negativeBorel ⊗[k] algebra G` and
`algebra p.positiveUnipotent ⊗[k] algebra G` are domains. The positive unipotent
subgroup is smooth (`dynamicSmooth`) with connected underlying space
(`DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent`).

`counit_borelCharacterCoordinate`: the extended character coordinate of every
`lam` has counit one, because a character takes the value `1` at the identity.

## Saturation

`IsRealizedBy.of_pow`: over an algebraically closed field, if `F` realizes
`n • lam` with `n > 0`, `f ^ n = F`, and `f` has counit one, then `f` realizes
`lam`. Left covariance comes from `mem_leftCovariantSubspace_of_pow` with
`p.negativeBorelHom` and the extended character coordinate of `lam`. The power
hypothesis is the covariance of `F` combined with
`pointAlgebraHom_borelCharacterCoordinate_nsmul`. Right invariance comes from
`mem_rightInvariantSubspace_of_pow` with `p.positiveUnipotentHom`, using the
right invariance of `F`. The required domain instances are the two tensor
lemmas above.

`IsRealizedWeight.of_nsmul`: over an algebraically closed field, if `n > 0` and
`p.IsRealizedWeight (n • lam)`, then `p.IsRealizedWeight lam`.

Proof. Let `F` realize `n • lam`, and let `x` be as in `exists_pow_eq_algebraMap`.
Send `x` to the fraction field `K` of the domain `algebra G` through
`IsLocalization.Away.lift`. This is possible because the cell coordinate is a
non-zero-divisor, hence nonzero, hence a unit in `K`. The image `y` satisfies
`y ^ n = algebraMap F`, which is integral. Since `algebra G` is integrally closed,
`y` comes from some `f₀ : algebra G`
(`IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow`), and
`f₀ ^ n = F` by injectivity into `K`. Its counit `c` satisfies `c ^ n = 1`, so
`c ≠ 0`. The normalized coordinate `c⁻¹ • f₀` still has `n`-th power `F` and has
counit one, and `IsRealizedBy.of_pow` shows that it realizes `lam`.

## The monoid of realized weights

`realizedWeights : AddSubmonoid (characterLattice p.torus)` is the set of
characters `lam` with `p.IsRealizedWeight lam`. It is closed under addition
(`IsRealizedWeight.add`, products of realizing coordinates) and contains `0`
(`isRealizedWeight_zero`, the constant coordinate `1`). `mem_realizedWeights`
unfolds membership.

`nsmul_mem_realizedWeights_iff`: over an algebraically closed field and for
`n > 0`, `n • lam ∈ p.realizedWeights` if and only if `lam ∈ p.realizedWeights`.
One direction is `IsRealizedWeight.of_nsmul`, and the other is closure of a
submonoid under multiples.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
