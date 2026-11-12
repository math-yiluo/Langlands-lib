# Base change of higher direct images along open immersions

Helper module for the proof of
`Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeStatement`
(see `FlatHigherDirectImageBaseChangeProof.md`). Namespace
`Langlands.AlgebraicGeometry.Modules.FlatBaseChange`.

## Declarations

- `isFlasque_restrictFunctor i N`: for an open immersion `i : U ⟶ X` and a
  module `N` with flasque underlying presheaf, the restriction
  `(Scheme.Modules.restrictFunctor i).obj N` is flasque. Its restriction maps
  are restriction maps of `N` (Mathlib's `Scheme.Modules.restrict_map`), which
  are epimorphisms. This generalizes the Library's `isFlasque_restrict` from
  `U.ι` to an arbitrary open immersion.
- `isZero_higherDirectImage_pullback_injective i g J r`: for an open immersion
  `i : U ⟶ X`, any `g : U ⟶ V` and an injective `J : X.Modules`,
  `R^{r+1} g_* (i^* J) = 0`. Injective modules are flasque (the Library's
  `PushforwardInjectiveAcyclic.isFlasque_of_injective`), so `i^* J`, isomorphic
  to the restriction by `Scheme.Modules.restrictFunctorIsoPullback i`, is
  flasque, and higher direct images of flasque modules vanish
  (`DerivedSections.isZero_higherDirectImage_of_isFlasque`).
- `isIso_higherDirectImageBaseChange_of_isOpenImmersion f j fV j' h M n`: for a
  cartesian square `h : IsPullback j' fV f j` with `j` an open immersion and
  pullbacks along `j` and `j'` preserving finite limits (instance arguments),
  the component at every module `M` of the published
  `higherDirectImageBaseChangeNatTrans j f fV j' h.w n` is an isomorphism, in
  every degree `n`. No quasi-compactness, separatedness or quasi-coherence is
  assumed.

## Proof of the open immersion case

`j'` is an open immersion as a base change of `j`. Let `I` be Mathlib's chosen
injective resolution of `M`. The second conjunct of the published
`resolutionCompatibility` is applied with `ε = I.ι`, the right resolution
`ε' = mapResolutionAugmentation j'^* I.ι` of `j'^* M` (a quasi-isomorphism by
the Library instance `quasiIso_mapResolutionAugmentation`, since `j'^*` is
exact), `ψ` the identity of `j'^* I` and
`Φ = resolutionBaseChangeMap τ ψ` for
`τ = pushforwardBaseChangeNatTrans j f fV j' h.w`. Its hypotheses hold:

- the terms of `I` are injective, hence `f_*`-acyclic
  (`Functor.isZero_rightDerived_obj_injective_succ`);
- the terms of `j'^* I` are `fV_*`-acyclic by
  `isZero_higherDirectImage_pullback_injective`;
- the components of `Φ` are the degree-zero base change maps
  `pushforwardBaseChange j f fV j' h.w (I.X q)`, isomorphisms for an open
  immersion by the Library's `isIso_pushforwardBaseChange_of_isOpenImmersion`,
  so `Φ` is an isomorphism and a quasi-isomorphism.

This is the derived form of the statement that higher direct images commute
with restriction to opens of the base (Stacks Project, Lemma 02KH, step 1).
The proof uses only the standard axioms.
