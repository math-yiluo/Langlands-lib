import Langlands.TraceFormula.WeilGeneralLinearCuspidalTransport
import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationProof

/-! # From cuspidal summands of Weil-restricted `GL_n` to cuspidal realizations over the upper field

The summand-to-realization direction for `W = Res_{L/K} GL_{r+1}`: transport an irreducible
closed cuspidal summand of `L²([W])` to the positive scalar quotient of `GL_{r+1}` over `L`
through the cuspidal comparison `cuspidalEquiv`, apply the untwisted theorem
`generalLinearCuspidalSummandRealization` there, and transport the resulting map back. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global AdelicGroupPoints AdelicWeilRestriction PositiveRealTorus
open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions Langlands.Analysis
open Langlands.Automorphic.GroupSchemeFunctions.WeilCuspidalTransport
open WeilGeneralLinearCuspidalTransport
open AdelicGroupAutomorphism

private local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

-- Keep the Weil group scheme opaque during instance synthesis.
set_option allowUnsafeReducibility true in
attribute [local irreducible] AffineWeil.groupScheme

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1400000 in
/-- **Irreducible cuspidal `L²` summands of `Res_{L/K} GL_{r+1}` come from cuspidal operator
realizations over `L`.** The summand is pulled back to the positive scalar quotient of
`GL_{r+1}` over `L` along the cuspidal comparison, where the untwisted theorem supplies the
realization; composing its map with the comparison gives the required map. -/
theorem weilGeneralLinearCuspidalSummandRealization :
    WeilGeneralLinearCuspidalSummandRealizationStatement.{u} := by
  intro K fK nK L fL nL alg _ _ r hPD hW T i hi hIndexK I finI e hc hHaarK S π Q hQ
  let : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions L (r + 1)) :=
    Submodule.addCommGroup _
  let : AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions L (r + 1)) :=
    Submodule.addCommGroup _
  let : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions L (r + 1)) :=
    Submodule.addCommGroup _
  let : AddCommGroup (Langlands.Automorphic.AutomorphicForms L (r + 1)) :=
    Submodule.addCommGroup _
  let : AddCommGroup (Langlands.Automorphic.StableAutomorphicFunctions L (r + 1)) :=
    Submodule.addCommGroup _
  let W := weilGroup K L (GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K))
  let affineW : IsAffine W.X.left := by
    let : IsAffineHom W.X.hom := hW.isAffineHom
    exact isAffine_of_isAffineHom W.X.hom
  let finiteW : LocallyOfFiniteType W.X.hom := by
    let : Smooth W.X.hom := hW.smooth
    infer_instance
  let G := GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of L)
  let hG := isConnectedReductive_generalLinear L (Fin (r + 1))
  let Z := Gm (Spec (CommRingCat.of L))
  let z := GeneralLinear.scalarTorus (Fin (r + 1)) (CommRingCat.of L)
  let hj := scalarCharacter_injective L r
  let hc' := scalar_isCentral L r
  let ez := splitTorus.gmIso (Spec (CommRingCat.of L))
  let w := weilIso K L r
  let hw := map_positiveImage K L r T i hi I e hc
  let hIndexL : (characterRestrict z).range.FiniteIndex := scalarCharacter_finiteIndex L r
  let hHaarL : (Measure.haar : Measure (normOneSubgroup L G)).IsMulRightInvariant :=
    normOneHaar_rightInvariant K L w
  let U := cuspidalEquiv K L w hw hi I e hc hj PUnit ez hc' hPD hW hG
  let πL := fullAEL2CuspidalBoundedRightAction L G hPD hG Z z hj PUnit ez hc'
  let a := ambientEquiv K L w
  -- The comparison, read backwards, intertwines the lower action at `a⁻¹ g` with the upper
  -- action at `g`.
  have hE : ∀ g x, U.symm (π (a.symm g) x) = πL g (U.symm x) := by
    intro g x
    have h := cuspidalEquiv_rightAction K L w hw hi I e hc hj PUnit ez hc' hPD hW hG
      (a.symm g) (U.symm x)
    apply U.symm_apply_eq.mpr
    exact (congrArg (fun y => π (a.symm g) y) (U.apply_symm_apply x).symm).trans
      (h.symm.trans (congrArg (fun g' => U (πL g' (U.symm x))) (a.apply_symm_apply g)))
  let P := Q.comap U.toLinearMap
  have hP : IsIrreducibleClosedSummand πL P :=
    IsIrreducibleClosedSummand.comap_symm_of_intertwining hQ U.symm a.symm a.symm.surjective hE
  obtain ⟨R, Ψ, hclass, hclosure⟩ :=
    generalLinearCuspidalSummandRealization L r hPD Z z hj PUnit ez hc' P hP
  let : AddCommGroup R.Space := Submodule.addCommGroup _
  let Ξ := U.toLinearMap ∘ₗ Ψ
  have hΞ (f : R.Space) :
      IsWeilFormClass K L r T i (Ξ f).val (R.realization.toContinuous f) := by
    change IsWeilFormClass K L r T i (U (Ψ f)).val (R.realization.toContinuous f)
    rw [cuspidalEquiv_val]
    exact (isWeilFormClass_iff K L r T i hi I e hc hw
      (R.realization.toContinuous f) (Ψ f).val).mpr (hclass f)
  have hC : (LinearMap.range Ξ).topologicalClosure = Q := by
    have hcomap : P.comap U.symm.toLinearMap = Q := Submodule.ext fun x => by
      change U (U.symm x) ∈ Q ↔ x ∈ Q
      exact iff_of_eq (congrArg (· ∈ Q) (U.apply_symm_apply x))
    change (LinearMap.range (U.toLinearMap ∘ₗ Ψ)).topologicalClosure = _
    exact (topologicalClosure_range_comp_equiv U Ψ).trans
      ((congrArg (Submodule.comap U.symm.toLinearMap) hclosure).trans hcomap)
  exact ⟨R, Ξ, hΞ, hC⟩

end Langlands.TraceFormula
