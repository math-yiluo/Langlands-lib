import Langlands.LocalFactor.BrauerKernel.GlobalAtV
import Langlands.LocalFactor.BrauerKernel.GlobalDimension
import Langlands.LocalFactor.BrauerKernel.BottomReduction
import Langlands.LocalFactor.BrauerKernel.Determinant
import Langlands.LocalFactor.BrauerKernel.RealizationPlace
import Langlands.LocalFactor.NonabelianBrauerKernelStatement
import Langlands.Global.Arithmetic.FieldRealizationProof
import Langlands.ClassFieldTheory.Local.ClassFormationAbsoluteCorestrictionProof
import Langlands.ClassField.Global.FundamentalClassProof
import Langlands.ClassField.Global.RelativeWeilCharacterFactorization
import Langlands.ClassField.Global.LocalRelativeWeilMapExistenceProof
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.Correspondence.RankOneEpsilonFieldTransport
import Langlands.ClassFieldTheory.Local.WeilTransferReciprocityProof

/-! # Brauer-kernel compatibility from the global argument -/

noncomputable section

set_option autoImplicit false

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global Langlands.Global.CompletionPadic Langlands.Global.AdelicFunctoriality
open ClassField.Global ClassField.Global.RelativeWeilGroup CommonClosure Correspondence
open scoped NumberField

attribute [local instance] relativeGaloisTopology

set_option maxHeartbeats 4000000 in
/-- **Bottom presentations.** Assume the existence of normalized local reciprocity families, the
transfer reciprocity of p-adic extensions, the existence of local-to-relative Weil maps and their
local transfer reciprocity. Then every presentation over the bottom field in the kernel of the
presentation map has trivial evaluation, for every additive character and Haar family. -/
theorem evaluationMap_eq_zero_bottom
    (hCC : LocalClassField.CommonClosureReciprocityExistence.{0})
    (hsq : LocalClassField.ExtensionWeilTransferReciprocityStatement.{0, 0})
    (hM : LocalRelativeWeilMapExistenceStatement.{0})
    (hN3 : LocalTransferReciprocityStatement.{0})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (z : Presentation F (baseExtension F))
    (hz : presentationMap.{uF, uV} F e _ z = 0)
    (ψ' : AdditiveCharacter F (baseExtension F)) (measures : HaarFamily F) :
    evaluationMap F _ ψ' measures z = 0 := by
  classical
  obtain ⟨D⟩ := nonempty_galoisTypeDecomposition.{uF, uV} F e he z hz
  have : Normal F.Carrier D.K.field := D.normal
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have hgal : IsGalois F.Carrier D.K.field := ⟨⟩
  -- the global realization of `D.K / F`
  let alg : Algebra F.Carrier (D.K.asPadicField (p := p)).Carrier :=
    (inferInstance : Algebra F.Carrier D.K.field)
  have htower : @IsScalarTower (Padic p) F.Carrier (D.K.asPadicField (p := p)).Carrier
      F.algebra.toSMul alg.toSMul (D.K.asPadicField (p := p)).algebra.toSMul :=
    @IsScalarTower.of_algebraMap_eq (Padic p) F.Carrier (D.K.asPadicField (p := p)).Carrier _ _ _
      F.algebra alg (D.K.asPadicField (p := p)).algebra fun _ => rfl
  have hgal' : IsGalois F.Carrier (D.K.asPadicField (p := p)).Carrier := hgal
  obtain ⟨k, K', _, _, _, _, _, _, -, hK'r, -, v, w, φ, ψ, θ, hwv, hwu, hφ, hφ', hψ, -, hcomp,
      hθ⟩ :=
    Global.totallyRealGaloisRealization.{uF, uF} p inferInstance F (D.K.asPadicField (p := p))
      alg htower hgal'
  have hp := residuePrime_eq_of_ringEquiv v F φ hφ'
  subst hp
  have := hwv
  have := hK'r
  -- the global class family
  let I : ∀ (q : ℕ) [Fact q.Prime], ClassFieldTheory.Local.InvariantFamily.{0, 0} q :=
    fun q _ => Classical.choose
      (ClassFieldTheory.Local.localAbsoluteCorestrictionCompatibleClassFormation.{0} q)
  have hI : ∀ (q : ℕ) [Fact q.Prime],
      (I q).RelativeClassFormation ∧ (I q).ArithmeticNormalization := fun q _ =>
    ⟨(Classical.choose_spec
        (ClassFieldTheory.Local.localAbsoluteCorestrictionCompatibleClassFormation.{0} q)).2.2.1,
      (Classical.choose_spec
        (ClassFieldTheory.Local.localAbsoluteCorestrictionCompatibleClassFormation.{0} q)).1⟩
  obtain ⟨c, hc, -⟩ := globalFundamentalClassStatement.{0}.2 I hI
  -- the Hecke characters of the Galois characters of the generators
  choose Θ₁ hΘ₁ using fun g => exists_eq_continuousReciprocityCharacter
    (transferCharacterFactorization c ⟨I, hI, hc⟩ (globalField D k K' θ g) K')
    (globalCharacter D c k K' θ hc.2.1 g (D.θ₁ g))
  choose Θ₂ hΘ₂ using fun g => exists_eq_continuousReciprocityCharacter
    (transferCharacterFactorization c ⟨I, hI, hc⟩ (globalField D k K' θ g) K')
    (globalCharacter D c k K' θ hc.2.1 g (D.θ₂ g))
  let gs : Fin z.support.card ≃ z.support := z.support.equivFin.symm
  -- the global argument
  obtain ⟨ψv, μv, α, hαv, -, hplace⟩ := exists_twist_placeEpsilonRatioProduct_eq_one
    hM hsq hCC I hI c hc (E := K') (fun i => z (gs i).1)
    (fun i => Finsupp.mem_support_iff.mp (gs i).2) (fun i => globalField D k K' θ (gs i).1)
    (fun i => D.t₁ (gs i).1) (fun i => D.t₂ (gs i).1) (fun i => Θ₁ (gs i).1)
    (fun i => Θ₂ (gs i).1)
    (fun i a => by
      rw [← hΘ₁ (gs i).1]
      exact globalCharacter_inclusion D c k K' θ hc.2.1 _ _ a)
    (fun i a => by
      rw [← hΘ₂ (gs i).1]
      exact globalCharacter_inclusion D c k K' θ hc.2.1 _ _ a)
    (fun α => globalRelation_generatorHecke.{uF, uV} D c k K' θ hc.2.1 gs α Θ₁ Θ₂
      (fun g => (hΘ₁ g).symm) (fun g => (hΘ₂ g).symm))
    (fun τ => ((Fintype.sum_equiv gs _ (fun j : z.support => z j.1 *
        (Module.finrank k (globalField D k K' θ j.1) : ℤ) *
        ((if D.t₁ j.1 = τ then 1 else 0) - (if D.t₂ j.1 = τ then 1 else 0)))
        fun _ => rfl).trans (Finset.sum_coe_sort z.support fun g => z g *
        (Module.finrank k (globalField D k K' θ g) : ℤ) *
        ((if D.t₁ g = τ then 1 else 0) - (if D.t₂ g = τ then 1 else 0)))).trans
      (globalField_type_dimension D k K' θ τ))
    v
  -- the distinguished place
  let ψF := PadicField.ConductorTransport.additiveCharacter (padicField v) F
    (realizationPadicEquiv v φ hφ) ψv
  have hψb : IsBaseCharacter F ψF (baseFieldAdditiveCharacterEquiv F ψF) :=
    (isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψF _).mpr rfl
  rw [evaluationMap_additiveCharacter_independent.{uF, uV} F e he _
    (baseFieldAdditiveCharacterEquiv F ψF) ψ' measures z hz]
  exact evaluationMap_eq_zero_of_placeEpsilon v D θ w φ ψ hφ hφ' hψ hcomp hθ hM hN3 hCC I hI c hc
    he hwu gs α hαv Θ₁ Θ₂ (fun g => (hΘ₁ g).symm) (fun g => (hΘ₂ g).symm) ψv μv hplace
    (baseFieldAdditiveCharacterEquiv F ψF) hψb measures

/-- **Brauer-kernel compatibility, conditionally.** Deligne's global argument (1973, proof of
Lemma 4.12) proves `KernelCompatibilityStatement` from the local transfer reciprocity of
local-to-relative Weil maps. The existence of normalized local reciprocity families, the transfer
reciprocity of p-adic extensions and the existence of local-to-relative Weil maps are the published
theorems `commonClosureReciprocityExistence`, `extensionWeilTransferReciprocity` and
`localRelativeWeilMapExistence`. -/
theorem kernelCompatibilityStatement_of_localTransferReciprocity
    (hN3 : LocalTransferReciprocityStatement.{0}) :
    KernelCompatibilityStatement.{uF, uV} := by
  intro p _ F e he E ψ measures z hz
  exact evaluationMap_eq_zero_of_bottom.{uF, uV} F e he
    (fun z' hz' ψ' measures' =>
      evaluationMap_eq_zero_bottom.{uF, uV} LocalClassField.commonClosureReciprocityExistence.{0}
        LocalClassField.extensionWeilTransferReciprocity.{0, 0} localRelativeWeilMapExistence.{0}
        hN3 F e he z' hz' ψ' measures')
    E ψ measures z hz

end Langlands.LocalFactor.NonabelianBrauer
