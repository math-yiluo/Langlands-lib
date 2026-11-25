/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.Curve.Reductions
import WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations
import WeilConjectures.AlgebraicGeometry.ReducedCurveNormalization
import WeilConjectures.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization

/-! # Reduction data for constant coefficients on reduced curves

The normalization argument is [Stacks 0A3Q](https://stacks.math.columbia.edu/tag/0A3Q).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve



/-- Reduction data for the normalization argument of Stacks 0A3Q, proof, first paragraph.
(blueprint: theorem-cohomology-curves)
The witnesses consist of a finite surjective smooth modification, a dense open where
it is an isomorphism, a pullback open immersion, and its eight lower-shriek assertions. -/
def ReducedConstantLowerShriekReductionData {k : Type u} [Field k] [IsAlgClosed k]
    {X U : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime] : Prop :=
  ∃ (Y : Scheme.{u}) (ν : Y ⟶ X) (V : X.Opens) (U' : Scheme.{u})
    (j' : U' ⟶ Y) (ν' : U' ⟶ U),
    IsFinite ν ∧ Surjective ν ∧ Smooth (ν ≫ f) ∧ Dense (V : Set X) ∧
      IsIso (ν ∣_ V) ∧ ∃ (hopen : IsOpenImmersion j'),
      IsPullback j' ν' ν j ∧
      IsCurve.Assertions (ULift.{u + 1} (ZMod r)) (ν ≫ f)
        ((@Etale.openImmersionLowerShriek _ _ _ _ U' Y j' hopen).obj
           (Etale.constantModSheaf (ULift.{u + 1} (ZMod r)) U' r))

/-- Transfer from smooth modification data.
Source: Stacks 0A3Q, proof, finite pushforward and dense-open comparison paragraphs;
`lemma-weil-pbc-curve-normalization-constant` records the existing transfer theorem.
(blueprint: k1-reduced-constant-lower-shriek-assertions-of-reduction-data)
Unpack the finite, surjective, smooth, dense-open-isomorphism and pullback hypotheses,
install their typeclass instances, and apply
`Assertions.lowerShriek_constantModSheaf_of_finite_coefficients` to the smooth assertion package. -/
theorem reducedConstantLowerShriekAssertions_of_reduction_data
    {k : Type u} [Field k] [IsAlgClosed k] {X U : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X] (j : U ⟶ X)
    [IsOpenImmersion j] (r : ℕ) [Fact r.Prime]
    (h : ReducedConstantLowerShriekReductionData f j r) :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        (Etale.constantModSheaf (ULift.{u + 1} (ZMod r)) U r)) := by
  obtain ⟨Y, ν, V, U', j', ν', hfinite, hsurj, hsmooth, hV, hiso,
    hopen, hpullback, H⟩ := h
  let := hfinite
  let := hsurj
  let := hsmooth
  let := hiso
  let := hopen
  exact Assertions.lowerShriek_constantModSheaf_of_finite_coefficients
    (ULift.{u + 1} (ZMod r)) f ν V hV j hpullback r H

/-- Existence of normalization data with smooth lower-shriek assertions.
Source: [Stacks 03SG](https://stacks.math.columbia.edu/tag/03SG), proof, and the
normalization paragraph of [Stacks 0A3Q](https://stacks.math.columbia.edu/tag/0A3Q).
(blueprint: k1-exists-reduced-constant-lower-shriek-reduction-data)
Proof:
1. Use `lem-weil-pbc-reduced-curve-normalization` to choose a finite surjective
modification with smooth composite and a dense open on which it is an isomorphism.
Form the pullback of j; the pullback immersion is open.
2. The smooth source is Noetherian (`lem-weil-pbc-finite-type-over-noetherian`) and
has finitely many components (`lem-weil-pbc-noetherian-finitely-many-components`).
Smoothness implies normality (`lemma-proper-smooth-model--1`), so the components are disjoint,
and their finite number makes each component open and closed.
3. On a component disjoint from the pullback open, extension by zero is zero.
Zero-dimensional components satisfy vanishing and field-extension comparison by
`lemma-sheaves-finite-support-finite-morphisms--1` and
`lemma-sheaves-finite-support-finite-morphisms--2`. On each remaining positive-dimensional
component the open is dense. Use `lemma-weil-pbc-smooth-curve-kummer-localization` for
r invertible in k and `lemma-weil-pbc-smooth-curve-artin-schreier` otherwise; these are
the characteristic branches of `proposition-p-torsion-smooth-proper-curve--1`. Apply
`lem-weil-pbc-curve-assertions-dense-open` to pass to extension by zero.
4. Apply the finite-pushforward case of the curve assertions to the component inclusions,
and `lemma-weil-pbc-eight-curve-devissage` to assemble their finite direct sum.
The quotient coefficient sheaf is the constant prime-field module sheaf, and all
comparison maps respect that coefficient identification. Package the witnesses and
the resulting assertions. Empty curves and empty intersections give zero sheaves. -/
theorem exists_reducedConstantLowerShriekReductionData
    {k : Type u} [Field k] [IsAlgClosed k] {X U : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X] (j : U ⟶ X)
    [IsOpenImmersion j] (r : ℕ) [Fact r.Prime] :
    ReducedConstantLowerShriekReductionData f j r := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : IsSeparated (X ↘ Spec (.of k)) := by
    change IsSeparated f
    infer_instance
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := by
    change LocallyOfFiniteType f
    infer_instance
  have : QuasiCompact (X ↘ Spec (.of k)) := by
    change QuasiCompact f
    infer_instance
  obtain ⟨Y, ν, hsep, hft, hqc, hdim, hsmooth, hfinite, V, hV, hiso⟩ :=
    exists_finite_smooth_modification_of_reduced_curve (k := k) X
      (IsCurve.krullDim_le_one (f := f))
  change IsSeparated (ν ≫ f) at hsep
  change LocallyOfFiniteType (ν ≫ f) at hft
  change QuasiCompact (ν ≫ f) at hqc
  change Smooth (ν ≫ f) at hsmooth
  let := hsep
  let := hft
  let := hqc
  let := hsmooth
  let := hfinite
  let := hiso
  let : IsCurve (ν ≫ f) := { krullDim_le_one := hdim }
  have hrange : (V : Set X) ⊆ Set.range ν := by
    intro x hx
    obtain ⟨y, hy⟩ := (ν ∣_ V).surjective ⟨x, hx⟩
    refine ⟨y.1, ?_⟩
    exact (morphismRestrict_base_coe ν V y).symm.trans (congrArg Subtype.val hy)
  have hsurj : Surjective ν := by
    constructor
    rw [← Set.range_eq_univ, ← ν.isClosedMap.isClosed_range.closure_eq]
    exact (hV.mono hrange).closure_eq
  let U' := pullback ν j
  let j' : U' ⟶ Y := pullback.fst ν j
  let ν' : U' ⟶ U := pullback.snd ν j
  have Hconstant : ∀ {C : Scheme.{u}} (g : C ⟶ Spec (.of k))
      [IsCurve g] [Smooth g],
      IsCurve.Assertions (ULift.{u + 1} (ZMod r)) g
        (Etale.constantModSheaf (ULift.{u + 1} (ZMod r)) C r) := by
    intro C g _ _
    by_cases hr : (r : k) = 0
    · let : CharP k r := (CharP.charP_iff_prime_eq_zero (Fact.out : r.Prime)).mpr hr
      exact assertions_constantModSheaf_of_charP (ULift.{u + 1} (ZMod r)) g r
    · exact assertions_constantModSheaf_of_ne_zero (ULift.{u + 1} (ZMod r)) g r hr
  refine ⟨Y, ν, V, U', j', ν', hfinite, hsurj, hsmooth, hV, hiso,
    inferInstance, IsPullback.of_hasPullback ν j, ?_⟩
  exact smoothConstantLowerShriekAssertions_of_constant r Hconstant (ν ≫ f) j'


/-- Prime coefficient sheaves are canonically isomorphic.
Source: `Etale.constantModSheaf` in `SmoothBaseChange.Defs`,
and Mathlib's `Submodule.quotEquivOfEqBot` and
`constantSheaf.mapIso` (the functorial image of a coefficient isomorphism).
(blueprint: theorem-cohomology-curves)
Proof: put Λ = ULift (ZMod r). Since r = 0 in Λ, the submodule generated by r is
zero. The map Λ/(r) to Λ sending a quotient class to its representative is therefore
well-defined and Λ-linear; its inverse sends an element to its quotient class.
The two composites are identities, by quotient induction and the quotient-by-zero
identity. Regard this linear equivalence as an isomorphism in ModuleCat, then apply
`(constantSheaf U.smallEtaleTopology (ModuleCat Λ)).mapIso` and unfold
`Etale.constantModSheaf`. This produces an isomorphism, not equality of objects. -/
theorem constantModSheaf_iso_constantSheaf {U : Scheme.{u}} (r : ℕ) [Fact r.Prime] :
    Nonempty (Etale.constantModSheaf (ULift.{u + 1} (ZMod r)) U r ≅
      (constantSheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod r)))) := by
  have hI : (Ideal.span {(r : ULift.{u + 1} (ZMod r))}) = ⊥ := by
    simp
  exact ⟨(constantSheaf U.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).mapIso
      ((Submodule.quotEquivOfEqBot _ hI).toModuleIso)⟩

end AlgebraicGeometry.IsCurve
