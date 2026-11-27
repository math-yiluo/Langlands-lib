# Finite étale covers of Weil-frame monodromy orbits

## A fixed lift under a factorization

`Langlands.AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_smul_eq_of_factor`:
let `f : T ⟶ S` be a morphism with geometric points `t` of `T` and `s` of `S`,
`t ≫ f = s`, let `Y` be a finite étale cover of `S` with a lift `y` of `s`, and
suppose `f = g ≫ Y.obj.hom` for some `g : T ⟶ Y.obj.left` with `t ≫ g = y.left`.
Then every element of the image of `π₁(T, t)` under `fundamentalGroupMap` fixes `y`.
The proof applies the published `fundamentalGroupMap_smul_left_of_comp` to the
trivial cover `cover (𝟙 T)`, whose fibre over `t` has the single element `t`
(every lift `z'` satisfies `z'.left ≫ 𝟙 = t`); hence the left side of the moved
lift is `t ≫ g = y.left`.

## Covers of orbits

The remaining declarations use the setting of the module `WeilFrameLevelMonodromy`
(arbitrary abelian scheme, dual data, polarization map, rational action `i`,
rational module `V` with form `ψ`, rational PEL conditions, a geometric point `s`
with finite geometric fibres), now with `V` in the universe of the base scheme and
`Module.Finite ℚ V`. Fix a frame `eta` and compact open levels `K`, `K'` of the
finite-adelic scalar-extension similitudes, and assume
`heta : RightOrbit.mk K.toSubgroup eta` is fixed by all of `π₁(S, s)`.

* `weilAdelicFrameOrbitAction eta K K' heta q` is the monodromy orbit of a raw
  `K'`-orbit `q`, as an object of `ContAction FintypeCat π₁(S, s)`: it is finite by
  `weilAdelicFrameOrbit_finite_of_fixed`, and the action is continuous for the
  discrete topology because stabilizers of orbit elements are the stabilizers of
  the underlying raw orbits, open by `weilAdelicFrameOrbit_stabilizer_isOpen_of_fixed`
  (`continuousSMul_iff_stabilizer_isOpen`).
* For connected locally Noetherian `S` and algebraically closed `Ω`,
  `weilAdelicFrameOrbitCover` is a preimage of this action under the published
  equivalence `geometricContinuousActionEquivalence` of `continuousActionFunctor`;
  `weilAdelicFrameOrbitCoverActionIso` is the comparison isomorphism of continuous
  actions, and `weilAdelicFrameOrbitCoverFiberEquiv` the induced bijection of the
  geometric fibre over `s` with the orbit. `weilAdelicFrameOrbitCoverFiberEquiv_smul`
  says it intertwines the fibre action with the orbit action.
* `weilAdelicFrameOrbitCoverPoint` is the lift corresponding to `q` itself
  (`weilAdelicFrameOrbitCoverFiberEquiv_point`), and
  `weilAdelicFrameOrbitCoverPoint_smul_eq` says that every element of `π₁(S, s)`
  fixing this lift fixes `q`: apply the equivariant fibre bijection.

Provenance: internal. The cover construction follows the module
`HarrisIntegralCMLevelOrbitCovers`, here for arbitrary Weil frames; the finite étale
input is the published Galois equivalence `geometricContinuousActionEquivalence` and
the fundamental-group functoriality of the module `FiniteEtale.Pullback`.
