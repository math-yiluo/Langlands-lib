import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.HarmonicAnalysis.FieldTransport
import Langlands.LocalField.PadicBridge
import Langlands.Representation.RankinSelberg.FieldTransport.LocalFieldEpsilon
import Langlands.Representation.RankinSelberg.GenericLanglandsPairEpsilonFactorComparisonProof

/-! # Identifying a completed equation's finite standard epsilon factor -/

noncomputable section

set_option autoImplicit false

universe uF uK uQ uV

namespace Langlands.Global.CuspidalPairFunctionalEquation

open scoped NumberField PadicField.CanonicalLocalField
open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear RankinSelberg
open Langlands.Correspondence Langlands.Global.CompletionPadic

section LocalTransport

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  {p : ℕ} [Fact p.Prime] (D : PadicField.{uK} p)
  (σ : F ≃+* D.Carrier) (hσ : Continuous σ) (hσs : Continuous σ.symm)

/-- Pull back the actual finite additive component, with no change of normalization. -/
abbrev completionAdditivePullback (ψ : NontrivialAdditiveCharacter D) :
    UnitaryAdditiveCharacter F :=
  HarmonicAnalysis.FieldTransport.additiveCharacter σ.symm hσ ψ

/-- Pull back the actual finite additive measure by inverse pushforward. -/
def completionHaarPullback (ν : LocalAdditiveHaarMeasure D) :
    letI := borel F; AdditiveHaarMeasure F := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  exact HarmonicAnalysis.FieldTransport.haarMeasure σ.symm hσs hσ ν

private theorem localField_totallyDisconnectedSpace (F : Type uF) [Field F]
    [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    TotallyDisconnectedSpace F := by
  let : T2Space F := HarmonicAnalysis.GeneralLocalField.t2Space F
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F)
  infer_instance

/-- The finite measure retains its intrinsic self-duality after pullback. -/
theorem completionHaarPullback_isSelfDual (ψ : NontrivialAdditiveCharacter D)
    (ν : LocalAdditiveHaarMeasure D) (hν : IsSelfDualMeasure D ψ ν) :
    letI := borel F; letI : BorelSpace F := ⟨rfl⟩
    letI : T2Space F := HarmonicAnalysis.GeneralLocalField.t2Space F
    letI : TotallyDisconnectedSpace F := localField_totallyDisconnectedSpace F
    IsSelfDual (completionAdditivePullback D σ hσ ψ) (completionHaarPullback D σ hσ hσs ν) := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : T2Space F := HarmonicAnalysis.GeneralLocalField.t2Space F
  let : TotallyDisconnectedSpace F := localField_totallyDisconnectedSpace F
  exact HarmonicAnalysis.FieldTransport.isSelfDual σ.symm hσs hσ ψ ν hν

private theorem completionHaarPullback_map (ν : LocalAdditiveHaarMeasure D) :
    letI := borel F; letI := borel D.Carrier
    ν.measure = (completionHaarPullback D σ hσ hσs ν).measure.map σ := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  exact (congrArg AdditiveHaarMeasure.measure
    (HarmonicAnalysis.FieldTransport.haarMeasure_symm σ.symm hσs hσ ν)).symm

variable {r : ℕ}
  (A : AutomorphicObject.{uK, uK} D r.succPNat)
  (B : AutomorphicObject.{uK, uK} D (Nat.succPNat 0))

/-- The actual Whittaker functionals for a `GL_(r+1) × GL₁` certificate make both
irreducible admissible representatives generic. The inverse unipotent character
on the second member is trivial, hence also standard. -/
private theorem isGeneric_of_standardPairCertificate (ψ : NontrivialAdditiveCharacter D)
    (ν : LocalAdditiveHaarMeasure D) {e : ℂˣ × ℤ}
    (h : RankinSelberg.IsPadicPairEpsilonFactor D ψ ν A.obj.representation B.obj.representation e) :
    IsGeneric ψ r A.obj.representation ∧ IsGeneric ψ 0 B.obj.representation := by
  let := borel (GeneralLinear 1 D.Carrier)
  let : BorelSpace (GeneralLinear 1 D.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent 1 D.Carrier)
  let : BorelSpace (upperUnipotent 1 D.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 D.Carrier)
  let π : Representation ℂ (GeneralLinear (r + 1) D.Carrier) A.obj := A.obj.representation
  let τ : Representation ℂ (GeneralLinear 1 D.Carrier) B.obj := B.obj.representation
  change IsPairEpsilonFactor D.canonicalTopologicalData.residueCardinality ψ
    (RankinSelberg.normalizedAbsoluteValue D.canonicalTopologicalData) ν π τ e at h
  have hf : HasFunctional (θ := standardCharacter ψ r) π ∧
      HasFunctional (θ := inverseStandardCharacter ψ 0) τ := by
    by_cases hr : r = 0
    · subst r
      have hh := (isPairEpsilonFactor_self (π := π) (σ := τ)).mp h
      exact ⟨hh.2.1, hh.2.2.1⟩
    · have hh := (isPairEpsilonFactor_of_lt (Nat.pos_of_ne_zero hr) (π := π) (σ := τ)).mp h
      exact ⟨hh.2.1, hh.2.2.1⟩
  have hθ : inverseStandardCharacter ψ 0 = standardCharacter ψ 0 := by
    ext g
    simp
  rw [hθ] at hf
  exact ⟨⟨A.property.1, A.property.2, hf.1⟩, ⟨B.property.1, B.property.2, hf.2⟩⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (a : ρ.Equiv (A.obj.representation.comp (Matrix.GeneralLinearGroup.map σ.toRingHom)))
  (b : Representation.Equiv (B.obj.representation.comp (Matrix.GeneralLinearGroup.map σ.toRingHom))
      (rankOneCharacter (1 : Fˣ →* ℂˣ)))

include a b in
/-- The class certificate and the supplied original standard JPSS certificate
have the same coefficient and exponent. No separate genericity assumption is
needed: the transported original certificate supplies the functionals. -/
theorem automorphicStandardEpsilon_eq_of_localCertificate
    (ψ : NontrivialAdditiveCharacter D) (ν : LocalAdditiveHaarMeasure D)
    (hν : IsSelfDualMeasure D ψ ν) {e e₀ : ℂˣ × ℤ}
    (he : IsAutomorphicPairEpsilonFactor D ψ ν (automorphicClassOf D A) (automorphicClassOf D B) e)
    (he₀ : AllField.RankinSelberg.IsPadicPairEpsilonFactor F
      (completionAdditivePullback D σ hσ ψ) (completionHaarPullback D σ hσ hσs ν)
      ρ (rankOneCharacter (1 : Fˣ →* ℂˣ)) e₀) : e = e₀ := by
  have hchar (x : F) : ψ (σ x) = completionAdditivePullback D σ hσ ψ x := rfl
  have hPull : AllField.RankinSelberg.IsPadicPairEpsilonFactor F
      (completionAdditivePullback D σ hσ ψ) (completionHaarPullback D σ hσ hσs ν)
      (A.obj.representation.comp (Matrix.GeneralLinearGroup.map σ.toRingHom))
      (B.obj.representation.comp (Matrix.GeneralLinearGroup.map σ.toRingHom)) e₀ := by
    let := borel F
    let : BorelSpace F := ⟨rfl⟩
    let := borel (GeneralLinear 1 F)
    let : BorelSpace (GeneralLinear 1 F) := ⟨rfl⟩
    let := borel (upperUnipotent 1 F)
    let : BorelSpace (upperUnipotent 1 F) := ⟨rfl⟩
    let := borel (LeftUnipotentQuotient 0 F)
    exact (IsPairEpsilonFactor.congr_equiv a b.symm).mp he₀
  have hE₀ : RankinSelberg.IsPadicPairEpsilonFactor D ψ ν A.obj.representation B.obj.representation e₀ :=
    (RankinSelberg.FieldTransport.isLocalPairEpsilonFactor_comp_iff σ hσ hσs hchar
      (completionHaarPullback_map D σ hσ hσs ν) A.obj.representation B.obj.representation e₀).mpr hPull
  obtain ⟨hA, hB⟩ := isGeneric_of_standardPairCertificate D A B ψ ν hE₀
  have hL := (isAutomorphicPairEpsilonFactor_iff D A B A.obj B.obj
    (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp he
  have hSym := genericLanglandsPairEpsilonFactorComparison.{uK, uK, uK}
    p D ψ ⟨ν, hν⟩ r 0 A.obj B.obj hA hB e hL
  exact ((RankinSelberg.isPadicSymmetricEpsilonFactor_of_le (Nat.zero_le r)).mp hSym).unique hE₀

end LocalTransport

section FinitePlace

variable {K : Type uK} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
  {r : ℕ} {T Td : Automorphic.CuspidalOperatorRealization K r}
  {T' Td' : Automorphic.CuspidalOperatorRealization K 0}
  {ψ : UnitaryAdditiveCharacter (Adeles K)}
  {P : Automorphic.CuspidalSpectralPresentation.{uK, uQ} T}
  {P' : Automorphic.CuspidalSpectralPresentation.{uK, uQ} T'}
  {Pd : Automorphic.CuspidalSpectralPresentation.{uK, uQ} Td}
  {Pd' : Automorphic.CuspidalSpectralPresentation.{uK, uQ} Td'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {hd : HasIrreducibleAdmissibleComponents Pd} {hd' : HasIrreducibleAdmissibleComponents Pd'}
  (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd') (v : FinitePlace K)
  {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  (σ : F ≃+* (padicField v).Carrier)
  (hσ : @Continuous F (padicField v).Carrier ‹TopologicalSpace F›
    (padicField v).canonicalTopologicalData.topology σ)
  (hσs : @Continuous (padicField v).Carrier F (padicField v).canonicalTopologicalData.topology
    ‹TopologicalSpace F› σ.symm)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (r + 1) F) V)

/-- Identification at a supplied distinguished completion of the finite factor
in the completed functional equation with the actual standard factor of `ρ`. -/
def DistinguishedFiniteStandardEpsilonStatement : Prop :=
  ρ.Equiv ((P.localComponent v).representation.comp (Matrix.GeneralLinearGroup.map σ.toRingHom)) →
  Representation.Equiv
      ((P'.localComponent v).representation.comp (Matrix.GeneralLinearGroup.map σ.toRingHom))
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) →
  ∀ e : ℂˣ × ℤ, AllField.RankinSelberg.IsPadicPairEpsilonFactor F
    (completionAdditivePullback (padicField v) σ hσ (c.additive v))
    (completionHaarPullback (padicField v) σ hσ hσs (c.measure v))
    ρ (rankOneCharacter (1 : Fˣ →* ℂˣ)) e →
    c.epsilon v = e ∧ ∀ z : ℂ, c.finiteEpsilon v z =
      epsilonMonomial (LocalFieldData.ofInstances F).residueCardinality e.1 e.2 z

theorem distinguishedFiniteStandardEpsilon : DistinguishedFiniteStandardEpsilonStatement c v σ hσ hσs ρ := by
  intro a b e he
  let D := padicField v
  let A := (P.localComponent v).padicObject (h v).1 (h v).2
  let B := (P'.localComponent v).padicObject (h' v).1 (h' v).2
  have hε := automorphicStandardEpsilon_eq_of_localCertificate D σ hσ hσs A B ρ a b
    (c.additive v) (c.measure v) (c.measure_spec v) (c.epsilon_spec v) he
  refine ⟨hε, fun z => ?_⟩
  have hq : residueCardinality v = (LocalFieldData.ofInstances F).residueCardinality :=
    (LocalFieldData.ofInstances F).residueCardinality_of_continuous_ringEquiv
      D.canonicalLocalFieldData σ hσ hσs
  simp only [FinitePairFactorChoice.finiteEpsilon, epsilonMonomial, hε, hq]

end FinitePlace

end Langlands.Global.CuspidalPairFunctionalEquation
