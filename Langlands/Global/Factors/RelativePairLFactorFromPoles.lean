import Langlands.Global.Factors.RelativePairLFactorPoleRoots
import Langlands.Global.Factors.RelativePairLFactorWitnessed
import Langlands.Global.Factors.RelativeIsometryOperationProof
import Langlands.Global.Factors.MeromorphicPoleComparisonProof
import Langlands.Correspondence.HenniartExtensionFactors
import Langlands.Correspondence.HenniartArithmeticTwistProof

/-! # Relative pair L-factors from certified poles of the unitary twists -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uF uW uP

namespace Langlands.Global.PoleComparison

open Polynomial RankinSelberg
open Langlands.ClassFieldTheory.Global Langlands.Global.CompletionPadic
open Langlands.Global.AdelicFunctoriality
open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Correspondence Langlands.Henniart.Extension Langlands.Weil.Local

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

local notation "K" => padicField v

private theorem exists_heckeExtension (χ : QuasiCharacter K) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    ∃ Ω : HeckeCharacter F, Ω.IsUnitary ∧
      ∀ a : (FiniteCompletion F v)ˣ, Ω.finiteComponent v a = χ a := by
  let f : (FiniteCompletion F v)ˣ →* ℂˣ :=
    @ContinuousMonoidHom.toMonoidHom _ _ _ _
      (@Units.instTopologicalSpaceUnits _ (padicField v).canonicalTopologicalData.topology _)
      _ χ
  let η : (FiniteCompletion F v)ˣ →ₜ* ℂˣ :=
    { toMonoidHom := f
      continuous_toFun := by
        change @Continuous _ _
          (@Units.instTopologicalSpaceUnits _ (inferInstanceAs
            (TopologicalSpace (FiniteCompletion F v))) _) _ f
        rw [completion_topology_eq v]
        exact @ContinuousMonoidHom.continuous_toFun _ _ _ _
          (@Units.instTopologicalSpaceUnits _
            (padicField v).canonicalTopologicalData.topology _) _ χ }
  obtain ⟨Ω, hΩ, hΩv⟩ := unitaryLocalCharacterExtension F v η (fun a => hχ a)
  exact ⟨Ω, hΩ, fun a => DFunLike.congr_fun hΩv a⟩

private theorem zeroMonodromy_twist_unramified_one
    (B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup K)) :
    WeilDeligneRepresentation.classOf
      (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom
        (FiniteRepresentation.twist (localUnramifiedCharacter K 1).toMonoidHom B)) =
      WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom B) := by
  have h1 : (localUnramifiedCharacter K 1).toMonoidHom = 1 := by
    apply MonoidHom.ext
    intro g
    change (1 : ℂˣ) ^ (localDegree K g).toAdd = 1
    exact one_zpow _
  rw [h1]
  exact (WeilDeligneRepresentation.classOf_eq_iff _ _).mpr
    ⟨WeilDeligneRepresentation.zeroMonodromyCongr _
      (Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => by
        change Langlands.twist 1 B.representation g = B.representation g
        rw [Langlands.twist_one])⟩

variable [CompactSpace (AdeleQuotient F)]

private local instance : TopologicalSpace (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.topology

private local instance (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

private local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopologicalGroup n

private abbrev localObject (d : WitnessedGenerator.{uF, uW, uP} F E c v) :
    AutomorphicObject.{uF, uF} K d.rankIndex.succPNat :=
  (d.presentation.localComponent v).padicObject d.local_irreducible d.local_admissible

omit [CompactSpace (AdeleQuotient F)] in
private theorem virtualPairLFactor_of_support
    {ψ : NontrivialAdditiveCharacter K} {ν : LocalAdditiveHaarMeasure K}
    (hν : IsSelfDualMeasure K ψ ν) {r t : ℕ}
    {A : SmoothRep.{0, uF, uF} ℂ (GeneralLinear (r + 1) (padicField v).Carrier)}
    {B : SmoothRep.{0, uF, uF} ℂ (GeneralLinear (t + 1) (padicField v).Carrier)}
    (hA : A.IsIrreducible) (hB : B.IsIrreducible)
    {x y : PadicSupercuspidal.UnitaryLattice.{uF, uF} K}
    (hx : PadicSupercuspidal.IsUnitaryLatticeSupport K A x)
    (hy : PadicSupercuspidal.IsUnitaryLatticeSupport K B y)
    {P : ℂ[X]} (hP : IsPadicSymmetricLPolynomial K ψ ν A.representation B.representation P) :
    PadicSupercuspidal.IsUnitaryPairLFactor K ψ ν x y
      ((algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹) := by
  obtain ⟨D, σ, hσ, ⟨eσ⟩⟩ :=
    PadicSupercuspidal.exists_equiv_unitarizableSupercuspidalProduct r.succ_pos hx
  obtain ⟨E, τ, hτ, ⟨eτ⟩⟩ :=
    PadicSupercuspidal.exists_equiv_unitarizableSupercuspidalProduct t.succ_pos hy
  exact PadicSupercuspidal.isUnitaryPairLFactor_of_equiv_productInduced ψ ν hν A B
    hA hB hx hy D σ hσ eσ E τ hτ eτ hP

set_option maxHeartbeats 1800000 in
/-- The poles of every unramified unitary twist determine the L-factor of a
witnessed generator paired with the dual of another witnessed generator. -/
theorem witnessed_isUnitaryPairLFactor_dual_of_poles
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    {ψ : NontrivialAdditiveCharacter K} {ν : LocalAdditiveHaarMeasure K}
    (hν : IsSelfDualMeasure K ψ ν)
    (D : RelativePairFactorData.{uF, uW, uP} F E c v ψ ν)
    (hD : RegularPairComparisonsAt D.comparison 0)
    (d e : WitnessedGenerator.{uF, uW, uP} F E c v) :
    PadicSupercuspidal.IsUnitaryPairLFactor K ψ ν d.automorphicElement
      (PadicSupercuspidal.unitaryContragredientLatticeEquiv K e.automorphicElement)
      (LocalWeil.unitaryPairLFactor K d.weilElement
        (LocalWeil.unitaryDualLatticeEquiv K e.weilElement)) := by
  let KD := (padicField v).canonicalTopologicalData
  let q := KD.residueCardinality
  have hq : 1 < q := KD.residueCardinality_gt_one
  let cofinal := GeneralLinear.compactOpen_cofinal K KD e.rankIndex.succPNat
  let B := IrreducibleAdmissibleRep.contragredient cofinal (localObject F E c v e)
  have hBclass : automorphicClassOf K B = D.dualClass e :=
    ((isSmoothDual_iff_eq_contragredient K _ _).mp (D.dual_spec e)).symm
  have hBsup : PadicSupercuspidal.IsUnitaryLatticeSupport K B.obj
      (PadicSupercuspidal.unitaryContragredientLatticeEquiv K e.automorphicElement) :=
    PadicSupercuspidal.isUnitaryLatticeSupport_contragredient K e.automorphic_support
  have hBtemp : KD.IsTempered B.obj.representation :=
    (witnessed_isTempered F E c v e).smoothContragredient
  have hsym (a : WitnessedGenerator.{uF, uW, uP} F E c v) : IsPadicSymmetricLPolynomial K ψ ν
      (localObject F E c v a).obj.representation B.obj.representation (D.polynomial a e) := by
    let A := localObject F E c v a
    have hP := D.polynomial_spec a e
    rw [← hBclass] at hP
    have hP' := (isAutomorphicPairLPolynomial_iff K A B A.obj B.obj
      (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp hP
    exact hP'.symmetric_of_tempered A.property.1 (witnessed_isTempered F E c v a)
      B.property.1 hBtemp
  let P := D.polynomial d e
  let WA := RelativeWeilGroup.localComponent d.weil d.localMap
  let WB := RelativeWeilGroup.localComponent e.weil.dual e.localMap
  let : (localInertia K).Normal := localInertia_normal K
  let normCharacter := (localNormCharacter K).toMonoidHom
  let Awd := WeilDeligneRepresentation.zeroMonodromy normCharacter WA
  let Bwd := WeilDeligneRepresentation.zeroMonodromy normCharacter WB
  let Cwd := WeilDeligneRepresentation.tensor Awd Bwd
  let Q := LocalFactor.WeilDeligne.eulerPolynomial Cwd (localInertia K) (localGeometricFrobenius K)
  have hQ0 : Q.coeff 0 = 1 := LocalFactor.WeilDeligne.eulerPolynomial_coeff_zero _ _ _
  have hQroots : ∀ z, Q.IsRoot z → ‖z‖ = 1 :=
    fun _ hz => weilDeligne_eulerPolynomial_root_norm Cwd
      (WeilDeligneRepresentation.tensor_isUnitary
        (RelativeWeilGroup.localComponent_isUnitary d.localMap d.weil_unitary)
        (RelativeWeilGroup.localComponent_isUnitary e.localMap
          (FiniteRepresentation.isUnitary_dual e.weil e.weil_unitary))) _ _ hz
  have hQ : arithmeticPairLFactor K (WeilDeligneRepresentation.classOf Awd)
      (WeilDeligneRepresentation.classOf Bwd) = (algebraMap ℂ[X] (RatFunc ℂ) Q)⁻¹ := rfl
  obtain ⟨rec, hrec, -⟩ := LocalClassField.geometricWeilReciprocityExistenceUniqueness
    (residuePrime v) K KD
  have hPQ : P = Q := by
    apply eq_of_unitCircle_rootMultiplicity (D.polynomial_spec d e).coeff_zero hQ0
    · exact fun _ => isPadicSymmetricLPolynomial_roots_of_unitarySupport hν
        (localObject F E c v d) B d.automorphic_support hBsup (hsym d)
    · exact hQroots
    intro z hz
    let zUnit := Units.mk0 z (by intro h; simp [h] at hz)
    obtain ⟨s₀, hs₀, habs⟩ := exists_unramifiedExponent K zUnit
    let χ := fieldUnramified K zUnit
    have hχ := norm_fieldUnramified K (w := zUnit) hz
    obtain ⟨Ω, hΩ, hΩv⟩ := exists_heckeExtension F v χ hχ
    obtain ⟨T, PT, hPT⟩ := Automorphic.cuspidalDeterminantMultiple F d.cuspidal d.presentation Ω
    have hassoc := RelativeWeilGroup.presentedDeterminantMultipleAssociation c hc
      F E d.weil d.cuspidal T d.presentation PT Ω hPT.1 d.associated
    let : d.placeOver.1.asIdeal.LiesOver v.asIdeal := d.placeOver.2
    have htransfer := RelativeWeilGroup.localTransferReciprocity c F E v d.placeOver.1
      d.reciprocity d.localMap d.localMap_spec
    let a := d.heckeTwist Ω χ hΩv T PT hPT hΩ rec hrec hχ htransfer hassoc
    have hχW :
        (RelativeWeilGroup.reciprocityCharacter c F E Ω).comp d.localMap.toMonoidHom =
          (localUnramifiedCharacter K zUnit).toMonoidHom := by
      rw [RelativeWeilGroup.reciprocityCharacter_comp_localMap Ω _ htransfer rec hrec χ hΩv,
        weilCharacter_fieldUnramified K hrec]
    have hEqW :
        RelativeWeilGroup.localPairClass a.weil a.localMap =
          WeilDeligneRepresentation.classOf
            (WeilDeligneRepresentation.zeroMonodromy normCharacter
              (FiniteRepresentation.twist (localUnramifiedCharacter K zUnit).toMonoidHom WA)) :=
      (WeilDeligneRepresentation.classOf_eq_iff _ _).mpr
        ⟨WeilDeligneRepresentation.zeroMonodromyCongr _
          (localComponentTwistEquiv F E c v d.weil d.localMap
            (RelativeWeilGroup.reciprocityCharacter c F E Ω)
            (localUnramifiedCharacter K zUnit) hχW)⟩
    have hWt := arithmeticPairLFactor_unramifiedTwist K WA WB zUnit 1 Q hQ
    rw [zeroMonodromy_twist_unramified_one F v WB, Units.val_one, mul_one] at hWt
    have hAt := (unramifiedTwistLFactor (residuePrime v) K ψ ⟨ν, hν⟩
      d.rankIndex e.rankIndex (localObject F E c v d).obj.representation
      B.obj.representation s₀ χ.toMonoidHom habs P (hsym d)).2
    rw [hs₀] at hAt
    have hasup := PadicSupercuspidal.isUnitaryLatticeSupport_characterTwist
      K d.automorphic_support χ hχ
    have haI := (isIrreducible_twist_iff (χ.toMonoidHom.comp GeneralLinear.determinant)
      (localObject F E c v d).obj.representation).mpr (localObject F E c v d).property.1
    have hAtL := virtualPairLFactor_of_support F v hν haI B.property.1 hasup hBsup hAt
    have haL := virtualPairLFactor_of_support F v hν (localObject F E c v a).property.1
      B.property.1 a.automorphic_support hBsup (hsym a)
    have hgraph := PadicSupercuspidal.isUnitaryPairLFactor_iff K ψ ν hν a.automorphicElement
      (PadicSupercuspidal.unitaryContragredientLatticeEquiv K e.automorphicElement)
    have hPL : D.polynomial a e = P.comp (C z * X) :=
      IsFractionRing.injective ℂ[X] (RatFunc ℂ)
        (inv_injective (((hgraph _).mp haL).trans (((hgraph _).mp hAtL).symm)))
    obtain ⟨hlm, hrm, hlu, hru, hlb, hrb, heq⟩ := hD a e
    have hord := completedPoleTransfer (FinitePlace F) (FinitePlace F)
      (D.leftPlaces a e) (D.rightPlaces a e) (D.comparison.left a e) (D.comparison.right a e)
      (D.leftOmitted a e) (D.rightOmitted a e) (D.leftBoundary a e) (D.rightBoundary a e)
      0 hlm hrm hlu hru hlb hrb heq
    change meromorphicOrderAt (relativeSpectralFunction F v
      (arithmeticPairLFactor K (RelativeWeilGroup.localPairClass a.weil a.localMap)
        (WeilDeligneRepresentation.classOf Bwd))) 0 =
      meromorphicOrderAt (relativeSpectralFunction F v
        ((algebraMap ℂ[X] (RatFunc ℂ) (D.polynomial a e))⁻¹)) 0 at hord
    rw [hEqW, hWt, hPL] at hord
    unfold relativeSpectralFunction at hord
    have hs : spectralPoint q s₀ = z := hs₀
    simp only [zUnit, Units.val_mk0] at hord
    rw [meromorphicOrderAt_rescaledPairLFactor hq Q (ne_zero_of_coeff_zero_eq_one hQ0) hs,
      meromorphicOrderAt_rescaledPairLFactor hq P (D.polynomial_spec d e).ne_zero hs] at hord
    exact_mod_cast neg_injective (WithTop.coe_inj.mp hord.symm)
  let : IsTopologicalGroup (RelativeWeilGroup c F E) := RelativeWeilGroup.isTopologicalGroup_krull
  have hBcont := (FiniteRepresentation.isContinuous_dual_iff e.weil).mpr e.associated.1
  rw [LocalWeil.unitaryPairLFactor_eq_of_expansion K _ _
    ⟨WA, RelativeWeilGroup.localComponent_isContinuous d.localMap d.associated.1⟩
    ⟨WB, RelativeWeilGroup.localComponent_isContinuous e.localMap hBcont⟩ d.weil_expansion
    (localExactExpansion_dual F E c v e.weil e.associated.1 hBcont e.localMap e.weilElement
      e.weil_expansion), hQ, ← hPQ]
  exact virtualPairLFactor_of_support F v hν (localObject F E c v d).property.1
    B.property.1 d.automorphic_support hBsup (hsym d)

/-- The certified pole comparisons give the L-factor clause of
`RelativeIsometryFactorStatement` for every requested self-dual measure. -/
theorem relativeIsometryPairLFactor_of_poles
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    {ψ : NontrivialAdditiveCharacter K}
    (hPole : RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ)
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v)
    (hT : RelativeGeneratedPositiveIsometry F E c v T)
    (ψ' : NontrivialAdditiveCharacter K) (ν' : LocalAdditiveHaarMeasure K)
    (hν' : IsSelfDualMeasure K ψ' ν')
    (x y : weilImage.{uF, uW, uP} F E c v) :
    PadicSupercuspidal.IsUnitaryPairLFactor K ψ' ν' (T x).1 (T y).1
      (LocalWeil.unitaryPairLFactor K x.1 y.1) := by
  let ν := localSelfDualHaar K ψ
  have hν := isSelfDual_localSelfDualHaar K ψ
  obtain ⟨D, hD, -, -⟩ := hPole.2 ν hν
  apply relativePairLFactor_of_witnessed F E c v T hT ψ' ν' hν' _ x y
  intro d e
  obtain ⟨ed, hW, hA⟩ := relativeWitnessedDualClosure_of_centralComparison F E c v hc
    RelativeWeilGroup.associatedCentralCharacter
    Automorphic.cuspidalUnitaryContragredientExistence
    Automorphic.cuspidalContragredientPresentationExistence
    Automorphic.cuspidalContragredientLocalCompatibility
    RelativeWeilGroup.presentedContragredientAssociation e
  have h := witnessed_isUnitaryPairLFactor_dual_of_poles F E c v hc hν D hD d ed
  rw [hW, hA, LocalWeil.unitaryDualLatticeEquiv_apply_apply,
    PadicSupercuspidal.unitaryContragredientLatticeEquiv_apply_apply] at h
  exact h.change hν hν'

/-- The pair L-factor comparison for the same inputs as
`RelativeIsometryFactorStatement`, with self-dual measure existence. -/
def RelativeIsometryPairLFactorStatement : Prop :=
  ∀ (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (c : FundamentalClass.ClassFamily.{uF}), RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (v : FinitePlace F) (ψ : NontrivialAdditiveCharacter (padicField v)),
    RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ →
  ∀ (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v),
    RelativeGeneratedPositiveIsometry F E c v T →
  ∀ ψ' : NontrivialAdditiveCharacter (padicField v),
    (∃ ν : LocalAdditiveHaarMeasure (padicField v), IsSelfDualMeasure (padicField v) ψ' ν) ∧
    ∀ (ν : LocalAdditiveHaarMeasure (padicField v)), IsSelfDualMeasure (padicField v) ψ' ν →
    ∀ x y : weilImage.{uF, uW, uP} F E c v,
      PadicSupercuspidal.IsUnitaryPairLFactor (padicField v) ψ' ν (T x).1 (T y).1
        (LocalWeil.unitaryPairLFactor (padicField v) x.1 y.1)

/-- Under the certified pole comparisons, every generated positive isometry
preserves the pair L-factor for each additive character and self-dual measure. -/
theorem relativeIsometryPairLFactor : RelativeIsometryPairLFactorStatement.{uF, uW, uP} := by
  intro F E _ _ _ _ _ _ _ c hc v ψ hPole T hT ψ'
  refine ⟨⟨localSelfDualHaar (padicField v) ψ',
    isSelfDual_localSelfDualHaar (padicField v) ψ'⟩, ?_⟩
  intro ν hν x y
  exact relativeIsometryPairLFactor_of_poles F E c v hc hPole T hT ψ' ν hν x y

end Langlands.Global.PoleComparison
