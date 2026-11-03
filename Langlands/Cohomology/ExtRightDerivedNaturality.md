# Coefficient naturality of the actual Ext/right-derived comparison

This internal prerequisite proves naturality in the second argument of the
existing comparison in `Langlands.Cohomology.ExtRightDerived`. It retains the
published comparison maps, including their use of Mathlib's actual derived
category Ext, and does not introduce a replacement cohomology theory.

## Objects, hypotheses and equations

Let `C : Type u` be an abelian category with morphisms in universe `v` and
`HasExt.{w} C`. For an object `X` put `P = preadditiveCoyoneda.obj (op X)`.
For an injective resolution `R` of `Y`, write

`K_R = (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex`.

The published additive equivalence `extAddEquivHomology X R n` identifies
`Ext.{w} X Y n` with `K_R.homology n`. For `f : Y ⟶ Z` and an actual
`InjectiveResolution.Hom R S f`, let `ψ` be the induced map from `K_R` to
`K_S`. For every natural number `n`, `extAddEquivHomology_naturality` proves

`extAddEquivHomology X S n (a.comp (Ext.mk₀ f) (add_zero n))`
`= HomologicalComplex.homologyMap ψ n (extAddEquivHomology X R n a)`.

`extAddEquivHomology_symm_naturality` proves the corresponding equation for
the inverse equivalences, on every homology class.

With the additional hypothesis `HasInjectiveResolutions C`, write
`E_Y = extAddEquivRightDerived X Y n`. The main theorem
`extAddEquivRightDerived_naturality` is

`E_Z (a.comp (Ext.mk₀ f) (add_zero n)) = (P.rightDerived n).map f (E_Y a)`.

The inverse theorem `extAddEquivRightDerived_symm_naturality` states

`E_Z.symm ((P.rightDerived n).map f b)`
`= (E_Y.symm b).comp (Ext.mk₀ f) (add_zero n)`.

These equations hold in all nonnegative degrees, including zero. Universes
`u`, `v`, and `w` are arbitrary, subject to the displayed category and Ext
instances. No geometric, finiteness, or coefficient acyclicity hypothesis is
added. Naturality in the first argument is not asserted.

## Natural isomorphism in the morphism universe

When `HasExt.{v} C` is supplied, Ext and the derived Hom functor both take
values in `AddCommGrpCat.{v}`. The definition `extRightDerivedNatIso X n`
constructs the natural isomorphism

`Abelian.extFunctorObj X n ≅ (P.rightDerived n)`.

Its components are exactly `(extAddEquivRightDerived X Y n).toAddCommGrpIso`;
`extRightDerivedNatIso_app` records that equality by reflexivity. The source
is Mathlib's actual Ext functor, whose map is postcomposition by `Ext.mk₀ f`.
`NatIso.ofComponents` uses the proved second-variable naturality equation.
This packaging uses Ext in universe `v`; the preceding elementwise theorems
retain independent Ext universe `w`.

## Cycle evaluation and implemented proof

`coyonedaHomComplex_cycles_coe` identifies the underlying Hom-complex cocycle
of a cycle of termwise Hom with `Cochain.fromSingleMk` of its cycle inclusion.
It uses the published `coyonedaHomComplexIso`, Mathlib's left homology data,
and naturality of the cycle inclusions.

`coyonedaHomologyAddEquiv_homologyπ` evaluates the existing Hom/cohomology-class
comparison on the class represented by such a cycle. This follows from
naturality of the homology projection and the projection identity for
`HomComplex.leftHomologyData`.

`extAddEquivHomology_symm_homologyπ` proves that the inverse resolution
comparison sends the class of a cycle `c` to
`R.extMk (K_R.iCycles n c) (n + 1) rfl hf`. Here `hf` is precisely the cocycle
condition supplied by `K_R.iCycles_d`. The proof transports `c` to the
integer-indexed complex using `extendCyclesIso` and the existing
`DerivedPlus.mapExtendIso`. Its inclusion is the original coefficient
composed with `R.cochainComplexXIso` inverse. The identity for the termwise
comparison is proved by substituting an index of the form `some n` in the
extension's object isomorphisms. Mathlib's `extEquivCohomologyClass_extMk`
then gives the desired cohomology class. Homology-projection naturality,
`homologyπ_extendHomologyIso_hom`, and cancellation of the mutually inverse
cycle maps transport that class back to `K_R`.

For a morphism of injective resolutions, surjectivity of the actual homology
projection reduces inverse naturality to this evaluation on cycles.
`InjectiveResolution.extMk_comp_mk₀` identifies the Ext map with composition
of the cycle coefficient by the resolution map in degree `n`.
`HomologicalComplex.cyclesMap_i` identifies precisely the same coefficient on
the homology side. Applying the existing additive equivalence gives forward
naturality.

For the actual right-derived comparison, the proof chooses the standard
injective resolutions and `InjectiveResolution.desc` of `f`. It combines the
resolution naturality equation with
`InjectiveResolution.isoRightDerivedObj_inv_naturality`. Thus it proves the
equation for the exact published composite, without changing its definition.
Inverse naturality follows by applying the forward equivalence and cancelling.

## Provenance and scope

This is derived internal API for published Library constructions, with no new
external source assertion. Its mathematical inputs are
`Langlands/Cohomology/ExtRightDerived.lean`,
`Langlands/Cohomology/DerivedPlus.lean`, and the pinned Mathlib APIs in
`CategoryTheory/Abelian/Injective/Ext.lean`,
`CategoryTheory/Abelian/RightDerived.lean`,
`Algebra/Homology/Embedding/ExtendHomology.lean`, and
`Algebra/Homology/HomotopyCategory/HomComplexCohomology.lean`.

The intended consumer is coefficient naturality of the existing
`AbelianSheafDerivedSections.HAddEquiv`, followed by the module comparison.
That assembly is not proved here. No compatibility with scheme base change,
long exact sequence boundaries, units, Picard fibres, or representability is
claimed. The host fppf Picard-sheaf representability theorem remains open.
