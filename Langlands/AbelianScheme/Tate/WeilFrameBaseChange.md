# Pointed base change of Weil-compatible adelic frames

Let `b : S' ⟶ S`, let `A` be an abelian scheme over `S`, and let
`s : Spec Ω ⟶ S'` be a field-valued point. Both bases are quasi-separated.
Write `A' = (baseChange b).obj A`, and equip its rational endomorphisms with the
actual pulled-back algebra action `i' = (rationalBaseChangeEnd b A).comp i`.
The dual-valued homomorphism of `A'` is
`lam' = canonicalDualValuedBaseChange … lam` from
[WeilAlongHomBaseChange](WeilAlongHomBaseChange.md). The tensor/Picard construction inputs,
Picard universal base change, actual dual representability/geometry/evaluation data,
and relative finite-Weil transition compatibility remain explicit.

## Frames and their value module

The source and target are the existing `WeilAdelicFrame` types for
`(A', lam', i', s)` and `(A, lam, i, s ≫ b)`. A frame is linear over
`D ⊗[ℚ] Global.FiniteAdeles ℚ`, with source `Global.FiniteAdeles ℚ ⊗[ℚ] V`, and satisfies
the existing `FormCompatible` predicate for the scalar-extended rational form `ψ` and
the actual Weil pullback. That predicate asserts the existence of a trivialization of
the actual twist value module; a trivialization is not retained as frame data.

`weilAdelicFrameBaseChange` is an equivalence between these frame types. It uses
`finiteAdeleAlgebraBaseChange` on the Tate target and the identity linear equivalence
on the twist. The twist is the same actual rational roots-of-unity limit at both ends,
because `(Over.mk s).left` and `(Over.mk (s ≫ b)).left` are the same scheme.
The full scalar comparison `h` is shared by both Tate modules and the twist.
The equation `adelicWeilAlongHomBilinearMap_baseChange`, reversed, supplies the
pairing hypothesis of the existing `FormIso.transport`.

The forward map postcomposes a frame with the actual rational Tate base-change map;
the inverse postcomposes with its inverse. The `_apply` and `_symm_apply` theorems
specify this pointwise. `weilAdelicFrameBaseChange_underlying` shows that forgetting
the form condition recovers exactly `adelicFrameBaseChange`, the existing comparison
on ambient tensor-linear frames. These equations are definitional after unfolding
the generic frame transport.

`weilPrimeToAdelicFrameBaseChange` is the analogous equivalence for
`WeilPrimeToAdelicFrame`, using `primeToFiniteAdeleAlgebraBaseChange`, the proved
away adelic pairing equation, and the identity on the actual away twist. One coupled
`hAway : PrimeToRationalProfiniteIntegerAdeleComparison h m` is used throughout.
The modulus `m` is any natural number. Its application, inverse-application and
underlying-frame equations have the same meaning with `Global.PrimeToFiniteAdeles m`.

## Right actions and subgroup orbits

`weilAdelicFrameBaseChange_right` and `weilPrimeToAdelicFrameBaseChange_right` prove
compatibility with the existing right action of source similitudes. Its convention
is `eta * g = eta ∘ g`. After subtype and linear-map extensionality the equations
are definitional: target postcomposition commutes with source precomposition.

For an arbitrary subgroup `U` of `ScalarExtensionSimilitudes D V R ψ`, where `R` is
the corresponding full or away adelic ring, `weilAdelicFrameRightOrbitBaseChange`
and `weilPrimeToAdelicFrameRightOrbitBaseChange` descend these equivalences to
right-orbit quotients using `RightOrbit.equiv`. Their `_mk` and `_symm_mk` equations
give the forward and inverse maps on representative classes. Neither direction
requires a fixed representative or a choice of a twist trivialization.

The `_translate` theorems commute with every existing level/Hecke map
`RightOrbit.translate g hg`. The source subgroup is `U`, the target is `U'`, and
the hypothesis is `∀ u ∈ U, g⁻¹ * u * g ∈ U'`. Each proof applies the generic
`RightOrbit.map_translate` to the proved right equivariance. The `_forget` theorems
specialize this square to `g = 1` and `U ≤ U'`, giving the usual map that forgets
level structure. Arbitrary subgroups are retained before any compact-open specialization.

## Provenance and scope

This is derived infrastructure from the existing Tate algebra base-change maps,
[AdelicFrameBaseChange](AdelicFrameBaseChange.md),
[WeilFrame](WeilFrame.md), [WeilAlongHomBaseChange](WeilAlongHomBaseChange.md),
and the generic [FormIsoTransport](../../Shimura/PEL/FormIsoTransport.md)
and [OrbitEquiv](../../Shimura/PEL/OrbitEquiv.md) constructions.
Harris–Taylor (2001), printed p.18 / PDF p.26, supplies the full and away Tate
rationalizations. Section III.1, printed pp.91–92 / PDF pp.99–100, defines the
pairing-compatible full and away frames used for PEL invariant-orbit level structures
and the right Hecke convention. The comparisons here are the explicit deductions
from Library constructions described above, rather than additional source assertions.

Here `D` is any rational algebra, `V` has compatible rational and `D`-module structures,
and `ψ` is any rational bilinear form. No finite-dimensionality, involution compatibility,
nondegeneracy, alternation or frame existence is asserted. Similarly `lam` is any actual
homomorphism into the constructed dual; this file does not establish a polarization
predicate. It compares the frame spaces and their right orbits. Geometric monodromy
fixedness, pointed maps on fixed level orbits, coherence for successive base changes,
compact-open topology, and canonical independence from an unpointed base point are
separate obligations.
