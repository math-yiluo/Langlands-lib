# Pointed pullback of actual Weil-compatible fixed level orbits

Let `b : S' ⟶ S`, let `A` be an abelian scheme over `S`, and let
`s : Spec Ω ⟶ S'` be a field-valued point. Both bases are quasi-separated.
The base-changed abelian scheme is `A' = (baseChange b).obj A`, with the actual
rational algebra action `i' = (rationalBaseChangeEnd b A).comp i` and the actual
homomorphism `lam' = canonicalDualValuedBaseChange … lam` into its constructed dual.
All tensor/Picard, dual representability/geometry/evaluation, Picard universal
base-change and relative finite-Weil transition inputs remain explicit.

This module constructs pointed base-change maps on the existing `WeilAdelicLevel`
and `WeilPrimeToAdelicLevel` sets, which consist of geometrically fixed right subgroup
orbits of actual Weil-compatible frames. It uses the full and away frame comparisons
from [WeilFrameBaseChange](WeilFrameBaseChange.md).

## Actual geometric actions and hypotheses

The left groups are the actual `FundamentalGroup s ht` over `S'` and
`FundamentalGroup (s ≫ b) hs` over `S`. Their map is
`fundamentalGroupMap b s (s ≫ b) rfl ht hs`, constructed from pullback of finite étale
covers. The witnesses `ht` and `hs` assert finiteness of every finite étale geometric
fibre at the respective field-valued points. No replacement acting group is introduced.

`htor : TorsionFiniteEtaleStatement` remains a named geometric theorem input.
In the full case `hu` and `hu'` assert invertibility on `S` and `S'` of every selected
positive order; in the away case they assert it only for orders coprime to the chosen
natural modulus `m`. Finite and étale instances for the actual roots-of-unity group
schemes at these orders are explicit on both bases. The existing frame monodromy
actions include the actual twist action when preserving compatibility.

The proof `rationalWeilGeometricTransport` from
[WeilGeometricTransportProof](WeilGeometricTransportProof.md) is supplied to these
existing monodromy actions and level definitions. Consequently callers do not need to
supply an additional proof of `RationalWeilGeometricTransportStatement`. Its tensor,
Picard, geometry, transition and finite-étaleness hypotheses are still the explicit
inputs described here. The same full comparison `h`, or the same coupled `hAway`, is
shared by both Tate modules and their actual twists.

## Equivariance and fixed-orbit pullback

`weilAdelicFrameBaseChange_monodromy` proves that the existing forward frame comparison
from the base-changed scheme to the original scheme intertwines the actual left actions
by the displayed fundamental-group map. The proof removes the compatibility proof field,
compares the underlying linear maps pointwise, and applies the published
`rationalBaseChange_monodromy` from
[PointedMonodromyBaseChangeProof](PointedMonodromyBaseChangeProof.md).
The underlying frame action is the rational Tate monodromy, so this proves the desired
frame equality without any additional assumption of that equality.
`weilPrimeToAdelicFrameBaseChange_monodromy` uses the same proof for the away selection.

`weilAdelicLevelBaseChange U` maps the original fixed level set at `s ≫ b` to the
base-changed fixed level set at `s`. It applies the already published
`InvariantOrbit.pullback` from [PointedFrameOrbitPullback](PointedFrameOrbitPullback.md)
to the actual group map, the actual compatible-frame equivalence, its right equivariance,
and the monodromy equation just proved. This generic construction sends the original
orbit class through the inverse right-orbit comparison. For each element of the new
fundamental group, equivariance and the original class's fixedness under its image prove
that the pulled-back class is fixed. Fixedness is never imposed on a representative.

The `_val` equation identifies the underlying map exactly with
`weilAdelicFrameRightOrbitBaseChange U` inverse on classes. The `_injective` theorem
follows from injectivity of that orbit equivalence's inverse and subtype extensionality.
It does not need surjectivity of `fundamentalGroupMap`.
`weilPrimeToAdelicLevelBaseChange`, its `_val` equation and `_injective` theorem provide
the same construction for the actual away fixed level sets.

## Hecke and level-forgetting squares

For arbitrary source and target subgroups `U` and `U'` of the respective source
similitude group, the `_translate` theorems commute with `InvariantOrbit.translate g hg`.
The condition is `∀ u ∈ U, g⁻¹ * u * g ∈ U'`, and the underlying frame convention is
`eta * g = eta ∘ g`. The proofs apply the existing `InvariantOrbit.pullback_translate`
to the same actual data. The `_forget` theorems specialize this to `g = 1` and `U ≤ U'`.
These equations concern fixed orbit classes and retain arbitrary subgroups before
compact-open specialization.

## Provenance and scope

This is an internal derivation from the Library's actual compatible-frame, monodromy,
pointed base-change, and invariant-orbit constructions named above.
Harris–Taylor (2001), printed p.18 / PDF p.26, gives the full and away Tate
rationalizations. Section III.1, printed pp.91–92 / PDF pp.99–100, motivates the
pairing-compatible frames and invariant-orbit PEL levels. The relative pullback maps
and their injectivity and Hecke squares are the explicit Library deductions described
here, rather than additional theorems attributed to that passage.

The map is an injection of fixed level sets; arbitrary pointed ground base change
need not give a bijection of them. No surjectivity of the fundamental-group map,
frame existence, chosen twist trivialization, nondegeneracy, alternation, polarization
predicate, or compact-open topology is asserted. The rational algebra `D`, its compatible
module `V`, and its rational bilinear form `ψ` are as general as the existing frame
interface permits. Coherence for successive ground base changes and canonical
independence from a geometric point remain separate obligations.
