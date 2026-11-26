import Langlands.TraceFormula.WeilGeneralLinearCuspidalTransport
import Langlands.Automorphic.GeneralLinearCuspidalRealizationSummandProof

/-! # From cuspidal realizations to cuspidal summands of Weil-restricted `GL_n` -/

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

local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

-- Keep the Weil group scheme opaque during instance synthesis.
set_option allowUnsafeReducibility true in
attribute [local irreducible] AffineWeil.groupScheme

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1400000 in
/-- A cuspidal realization over the upper field that descends to the given lower
positive rational quotient generates a closed irreducible cuspidal `L²` summand there. -/
theorem weilGeneralLinearCuspidalRealizationSummand :
    WeilGeneralLinearCuspidalRealizationSummandStatement.{u} := by
  intro K fK nK L fL nL alg _ _ r hPD hW T i hi hIndexK I finI e hc hHaarK S π Φ R hdesc
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
  let : AddCommGroup R.Space := Submodule.addCommGroup _
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
  have hdesc' (f : R.Space) :
      ∃ h : C(PositiveRationalQuotient L G Z z, ℂ),
        continuousGeneralLinearEquiv L (r + 1) (positiveQuotientContinuousPullback L G Z z h) =
          R.realization.toContinuous f :=
    (descends_iff K L r T i hw (R.realization.toContinuous f)).mp (hdesc f)
  obtain ⟨P, Ψ, hP, hclass, hclosure⟩ :=
    generalLinearCuspidalRealizationSummand L r hPD Z z hj PUnit ez hc' R hdesc'
  let U := cuspidalEquiv K L w hw hi I e hc hj PUnit ez hc' hPD hW hG
  let Q : Submodule ℂ S := P.comap U.symm.toLinearMap
  let Ξ := U.toLinearMap ∘ₗ Ψ
  let transport := @cuspidalEquiv_irreducibleSummand K L fK nK fL nL alg
    G inferInstance inferInstance W affineW finiteW w T i Z z hw hi hIndexK I finI e hc
    hj hIndexL PUnit inferInstance ez hc' hPD hW hG hHaarK hHaarL
  let transportP := transport P
  have hQ : IsIrreducibleClosedSummand π Q := transportP hP
  have hΞ (f : R.Space) :
      IsWeilFormClass K L r T i (Ξ f).val (R.realization.toContinuous f) := by
    change IsWeilFormClass K L r T i (U (Ψ f)).val (R.realization.toContinuous f)
    rw [cuspidalEquiv_val]
    exact (isWeilFormClass_iff K L r T i hi I e hc hw
      (R.realization.toContinuous f) (Ψ f).val).mpr (hclass f)
  have hC : (LinearMap.range Ξ).topologicalClosure = Q := by
    change (LinearMap.range (U.toLinearMap ∘ₗ Ψ)).topologicalClosure = _
    exact (topologicalClosure_range_comp_equiv U Ψ).trans
      (congrArg (Submodule.comap U.symm.toLinearMap) hclosure)
  exact ⟨Q, Ξ, hQ, hΞ, hC⟩

end Langlands.TraceFormula
