# The type `F₄` Hasse kernel from toral reductions

Module `Langlands.GroupScheme.Rational.NumberFieldTypeF4HasseToralReduction`, namespace
`Langlands.GroupScheme`, one universe parameter `u`.

## Statement

```lean
def NumberFieldTypeF4HasseToralReductionStatement : Prop :=
  NumberFieldQuaternionicSpinHasseStatement.{u} →
    NumberFieldTrialitarianTypeDHasseStatement.{u} →
    TypeF4LongRootSubgroupStatement.{u} →
    NumberFieldQuadraticToralReductionStatement.{u} →
    NumberFieldTypeF4HasseStatement.{u}
```

The proposition says that the Hasse kernel for simply connected absolutely almost-simple
groups of type `F₄` over number fields (`NumberFieldTypeF4HasseStatement`, module
`Rational.NumberFieldHasseKernelTypeReduction`: every cocycle on a finite Galois field cover
that is trivial at every place is trivial) follows, at the same universe, from four
statements:

- `NumberFieldQuaternionicSpinHasseStatement` (module
  `Rational.NumberFieldClassicalTypeDHasseReduction`): the Hasse kernel of spin groups of
  nondegenerate quadratic forms of rank at least four over a quaternion division algebra with
  an orthogonal involution over a number field;
- `NumberFieldTrialitarianTypeDHasseStatement` (module
  `Rational.NumberFieldHasseKernelTypeReduction`): the Hasse kernel of the trialitarian forms
  `³D₄` and `⁶D₄`;
- `TypeF4LongRootSubgroupStatement` (module `SimplyConnected.TypeF4LongRootSubgroupStatement`):
  over a field of characteristic zero, every maximal torus of a simply connected absolutely
  almost-simple group of type `F₄` lies in a closed simply connected absolutely almost-simple
  subgroup of type `D₄`;
- `NumberFieldQuadraticToralReductionStatement` (module
  `Rational.NumberFieldQuadraticToralReductionStatement`): over a number field, a cocycle of a
  connected reductive group on a quadratic Galois cover that is trivial at the real places is
  cohomologous to the image of a cocycle of a maximal torus that is trivial at the real places.

The module proves the implication (theorems `numberFieldTypeF4HasseToralReduction` and
`numberFieldTypeF4Hasse_of_longRoot_quadratic`) and none of the four premises. This is the
route of Platonov–Rapinchuk §6.8 for type `F₄` (see Sources); the two structural premises
isolate the facts that route uses about the long-root subgroup and about Lemma 6.28.

## Declarations

- `numberFieldTypeD4Hasse_of_quaternionic_trialitarian`. The Hasse kernel for a simply
  connected absolutely almost-simple group over a number field with a Tits index numbered by
  `CartanMatrix.D 4`. If the full star action fixes a leaf, the published reduction
  `numberFieldClassicalTypeDHasse_of_quaternionic` applies after renumbering with
  `TitsIndexData.d4NumberingAt`; otherwise the group is trialitarian and the trialitarian
  kernel applies. This is the type `D₄` case analysis of
  `numberFieldAbsolutelyAlmostSimpleSimplyConnectedGaloisHasseKernel_of_types`.
- `typeF4_torusCocycle_isTrivial`. Let `G` be of type `F₄` over a number field, `T` a maximal
  torus and `η` a cocycle of `T` on a finite Galois cover that is trivial at every real place.
  Then the image of `η` in `G` is trivial. The long-root statement gives a simply connected
  subgroup `H ⊇ T` of type `D₄`. The image of `η` in `H` is trivial at the real places, hence
  at every place by `simplyConnectedRealToAllPlacesComparison`, so it is trivial by the type
  `D₄` kernel.
- `typeF4_center_eq_bot`. A simply connected group with a Tits index numbered by
  `CartanMatrix.F₄` has trivial full centre. By
  `TitsIndexData.natCard_centerCharacter_eq_cartanDet` and `CartanMatrix.F₄_det` the quotient
  of the absolute character lattice by the root span has one element, so the roots span the
  character lattice. `center_eq_bot_of_full_rootSpan` gives a trivial centre over the
  separable closure, and `center_eq_bot_baseChange_iff` descends it.
- `typeF4_quasiSplit_totallyComplex_isTrivial`. Over a number field without real places,
  every finite-Galois cocycle of a quasi-split group of type `F₄` is trivial. The published
  `quasiSplitCocycleTorusReduction` (Steinberg) moves a refinement of the cocycle into a closed
  torus, `exists_maximalTorus_extension_of_finiteType` puts that torus in a maximal torus, and
  the torus lemma applies with an empty real-place condition.
- `IsAdjointQuotient.isIso_of_center_eq_bot`. An adjoint quotient of a group with trivial full
  centre is an isomorphism, by the group universal property applied to the identity.
- `LocalGroupIso.hasInnerDiscrepancy_of_hasDiscrepancy`. A local isomorphism whose
  discrepancy is given by a cocycle of an acting group has inner discrepancy.
- `typeF4_totallyComplex_isTrivial`. Over a number field without real places, every
  finite-Galois cocycle of a group of type `F₄` is trivial. Take the quasi-split inner form of
  `quasiSplitInnerFormExistence`. Its model `H` is simply connected and absolutely almost
  simple by field-extension reflection along the local isomorphism, and
  `innerFormStarAction` gives a root-datum equivalence preserving the bases, so a Tits index of
  `H` is numbered by `CartanMatrix.F₄`. Its centre is trivial, so its adjoint quotient is an
  isomorphism and the adjoint discrepancy cocycle becomes a cocycle of `H`, trivial by the
  quasi-split case. Hence the group is quasi-split (`QuasiSplitInnerForm.isQuasiSplit_of_isTrivial`)
  and the quasi-split case applies to it.
- `exists_totallyComplex_quadratic`. A number field with a real place has, inside its
  separable closure, a quadratic totally complex extension: adjoin a square root of `-1`.
- `numberFieldTypeF4Hasse_of_longRoot_quadratic`. The main theorem, the implication with the
  four premises as explicit hypotheses; its proof is described below.
- `numberFieldTypeF4HasseToralReduction`. The proposition
  `NumberFieldTypeF4HasseToralReductionStatement`, obtained from the main theorem.

## Proof of the main theorem

Let `ξ` be a locally trivial cocycle of a group `G` of type `F₄` over a number field `F`, on a
finite Galois cover `Spec L`. If `F` has no real place, `typeF4_totallyComplex_isTrivial`
applies. Otherwise let `E = F(√-1)`, a quadratic totally complex extension inside the
separable closure, and let `M` be the splitting field over `E` of the minimal polynomial of a
primitive element of `L/F`. Then `M/E` is finite Galois and `L` embeds into `M` over `F`.

1. Refine `ξ` to `Spec M` and base change it to `E`, with the cover `Spec M → Spec E`. The
   base change of `G` is again of type `F₄`: simple connectedness and absolute almost
   simplicity ascend, and `TitsIndexData.prescribedStabilizerIndexComparison` gives a Tits
   index over `E` with the same Cartan matrix. By `typeF4_totallyComplex_isTrivial` the base
   change is trivial.
2. By `Cocycle.exists_of_baseChange_isTrivial`, a twist of the refined cocycle is trivial on
   pairs of points of `Spec M` with the same image in `Spec E`. By
   `Cocycle.exists_refine_eq_of_comp_eq` it is the refinement of a cocycle `ν` on the quadratic
   cover `Spec E → Spec F`.
3. At each real place `ξ` is trivial, so the refined and twisted cocycle is trivial there, and
   `Cocycle.Cohomologous.of_refine_fpqcCover` descends this to `ν`.
4. The quadratic toral reduction gives a maximal torus `T` and a cocycle `θ` of `T` on
   `Spec E`, trivial at the real places, with `ν` cohomologous to its image. The torus lemma
   makes that image trivial, so `ν`, its refinement and `ξ` are trivial; the last step uses
   `Cocycle.isTrivial_refine_iff` for the field extension `M/L`.

## Sources

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press 1994,
registered as `platonov-rapinchuk-1994-algebraic-groups-number-theory` (printed page `p` is
PDF page `p + 10`). §6.8, printed p. 371, treats type `F₄`: over a local field or a totally
imaginary number field every class of the quasi-split form comes from a maximal torus
(Proposition 6.19, Steinberg), which lies in the simply connected long-root subgroup of type
`D₄`; and over a number field with real places the argument for type `G₂` on printed
pp. 369–370 is repeated, passing to `K(√-1)` and using Lemma 6.28. The Lean proof follows this
route with three differences: the quasi-split form is reached through the Library's
quasi-split inner form and the trivial centre rather than through the uniqueness of the form;
the quadratic step uses the toral reduction without a Borel subgroup; and only real places are
controlled in that step, the finite places being handled by the local vanishing theorem
inside `simplyConnectedRealToAllPlacesComparison`.
