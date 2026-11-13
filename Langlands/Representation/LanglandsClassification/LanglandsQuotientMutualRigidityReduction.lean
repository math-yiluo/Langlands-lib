import Langlands.Representation.LanglandsClassification.LanglandsClassificationStatement
import Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityReduction
import Langlands.Representation.LanglandsClassification.RegularOppositeLanglandsHead
import Langlands.Representation.LanglandsClassification.OppositeLeviParabolic
import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement
import Langlands.Representation.Intertwining.OppositeIdentitySupportProof

/-! # Langlands quotient injectivity from two-sided opposite intertwining rigidity

Renard VII.4.2 (ii) passes through the diagram (VII.4.2.1): a common irreducible
quotient `π` of `i_{P₁}^G(σ₁ ψ₁)` and `i_{P₂}^G(σ₂ ψ₂)` embeds into the opposite
induction `i_{P̄₂}^G(σ₂ ψ₂)`, and also into `i_{P̄₁}^G(σ₁ ψ₁)`. The two
composites are nonzero intertwiners `i_{P₁}^G(σ₁ ψ₁) → i_{P̄₂}^G(σ₂ ψ₂)` and
`i_{P₂}^G(σ₂ ψ₂) → i_{P̄₁}^G(σ₁ ψ₁)`. The proposition
`LanglandsTripletMutualOppositeIntertwiningRigidityStatement` asserts that the
existence of both maps forces the conclusion of part (ii). The theorem
`langlandsQuotientInjective_of_mutualRigidity` derives the exact part (ii) from it,
second adjointness and the opposite kernel part of VII.4.1.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Two-sided form of the part of the proof of Renard VII.4.2 (ii) after the diagram
(VII.4.2.1). Take two Langlands triplets `(P₁ = M₁U₁, σ₁, ψ₁)` and `(P₂ = M₂U₂, σ₂, ψ₂)`
relative to the same choices. For each `j`, let `Qⱼ = MⱼVⱼ` be an actual parabolic opposite
to `Pⱼ` with the same Levi. Suppose there are nonzero intertwining maps
`i_{P₁}^G(σ₁ ⊗ ψ₁) → i_{Q₂}^G(σ₂ ⊗ ψ₂)` and `i_{P₂}^G(σ₂ ⊗ ψ₂) → i_{Q₁}^G(σ₁ ⊗ ψ₁)`. Then
`J₁ = J₂`, `|ψ₁| = |ψ₂|` on common Levi points, and `σ₁ ⊗ ψ₁ ≅ σ₂ ⊗ ψ₂` over the common
Levi points. The conclusion is literally that of `LanglandsQuotientInjectiveStatement`. -/
def LanglandsTripletMutualOppositeIntertwiningRigidityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of k)))
      (A₁ : CommGroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M₁ ⟶ P₁) (r₁ : U₁ ⟶ P₁) (a₁ : A₁.toGrp ⟶ M₁)
      (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
      (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (hmul₁ : IsIso (subgroupMultiplication l₁ r₁)) (ha₁ : IsSplitComponent a₁)
      (J₁ : Set (characterLattice T)) (f₁ : A₁ ⟶ T)
      (σ₁ : letI := leviPointTopology l₁ hl₁; SmoothRep.{0, u, v} ℂ (rationalPoints M₁))
      (ψ₁ : leviUnramifiedCharacters l₁ hl₁)
      (P₂ M₂ U₂ : GroupScheme (Spec (CommRingCat.of k)))
      (A₂ : CommGroupScheme (Spec (CommRingCat.of k)))
      (p₂ : P₂ ⟶ G) (l₂ : M₂ ⟶ P₂) (r₂ : U₂ ⟶ P₂) (a₂ : A₂.toGrp ⟶ M₂)
      (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
      (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
      (hmul₂ : IsIso (subgroupMultiplication l₂ r₂)) (ha₂ : IsSplitComponent a₂)
      (J₂ : Set (characterLattice T)) (f₂ : A₂ ⟶ T)
      (σ₂ : letI := leviPointTopology l₂ hl₂; SmoothRep.{0, u, v} ℂ (rationalPoints M₂))
      (ψ₂ : leviUnramifiedCharacters l₂ hl₂)
      (Q₁ V₁ : GroupScheme (Spec (CommRingCat.of k)))
      (q₁ : Q₁ ⟶ G) (lQ₁ : M₁ ⟶ Q₁) (rQ₁ : V₁ ⟶ Q₁)
      (hq₁ : IsParabolicSubgroup q₁) (hlQ₁ : IsRationalLeviSubgroup lQ₁)
      (hrQ₁ : LeviSubgroup.IsGeometricUnipotentRadical rQ₁)
      (hmulQ₁ : IsIso (subgroupMultiplication lQ₁ rQ₁))
      (Q₂ V₂ : GroupScheme (Spec (CommRingCat.of k)))
      (q₂ : Q₂ ⟶ G) (lQ₂ : M₂ ⟶ Q₂) (rQ₂ : V₂ ⟶ Q₂)
      (hq₂ : IsParabolicSubgroup q₂) (hlQ₂ : IsRationalLeviSubgroup lQ₂)
      (hrQ₂ : LeviSubgroup.IsGeometricUnipotentRadical rQ₂)
      (hmulQ₂ : IsIso (subgroupMultiplication lQ₂ rQ₂)),
      lQ₁ ≫ q₁ = l₁ ≫ p₁ →
      pointImage p₁ ⊓ pointImage q₁ = pointImage (l₁ ≫ p₁) →
      lQ₂ ≫ q₂ = l₂ ≫ p₂ →
      pointImage p₂ ⊓ pointImage q₂ = pointImage (l₂ ≫ p₂) →
      IsLanglandsTriplet i ν D p₁ l₁ a₁ hp₁ hl₁ ha₁ J₁ f₁ σ₁ ψ₁ →
      IsLanglandsTriplet i ν D p₂ l₂ a₂ hp₂ hl₂ ha₂ J₂ f₂ σ₂ ψ₂ →
        letI : TopologicalSpace (rationalPoints M₁) := leviPointTopology l₁ hl₁
        haveI : NonarchimedeanGroup (rationalPoints M₁) :=
          leviPoints_nonarchimedeanGroup p₁ l₁ hp₁ hl₁
        letI : TopologicalSpace (rationalPoints M₂) := leviPointTopology l₂ hl₂
        haveI : NonarchimedeanGroup (rationalPoints M₂) :=
          leviPoints_nonarchimedeanGroup p₂ l₂ hp₂ hl₂
        let τ₁ := σ₁.twist ψ₁.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₁)
        let τ₂ := σ₂.twist ψ₂.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₂)
        ∀ t₁ : ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj τ₁).representation.IntertwiningMap
            ((leviInductionFunctor q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂).obj τ₂).representation,
          t₁ ≠ 0 →
        ∀ t₂ : ((leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj τ₂).representation.IntertwiningMap
            ((leviInductionFunctor q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj τ₁).representation,
          t₂ ≠ 0 →
            J₁ = J₂ ∧
            (∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
              rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
                ‖(ψ₁.val m₁ : ℂ)‖ = ‖(ψ₂.val m₂ : ℂ)‖) ∧
            ∃ φ : τ₁ ≃ₗ[ℂ] τ₂,
              ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
                rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
                  ∀ x : τ₁, φ (τ₁.representation m₁ x) = τ₂.representation m₂ (φ x)

/-- Renard VII.4.2 (ii) from second adjointness, the opposite kernel part of VII.4.1 and
two-sided opposite intertwining rigidity. The common irreducible quotient embeds into the
opposite induction of each triplet. Composing each embedding with the quotient map from
the other triplet gives the two nonzero intertwiners, to which rigidity applies. Opposite
identity support is the proved `oppositeIdentitySupport`. -/
theorem langlandsQuotientInjective_of_mutualRigidity
    (hAdj : LeviSecondAdjointnessStatement.{u, v})
    (hK : LanglandsTripletOppositeKernelStatement.{u, v})
    (hR : LanglandsTripletMutualOppositeIntertwiningRigidityStatement.{u, v}) :
    LanglandsQuotientInjectiveStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D P₁ M₁ U₁ A₁ p₁ l₁ r₁ a₁ hp₁ hl₁ hr₁ hmul₁ ha₁ J₁ f₁ σ₁ ψ₁
    P₂ M₂ U₂ A₂ p₂ l₂ r₂ a₂ hp₂ hl₂ hr₂ hmul₂ ha₂ J₂ f₂ σ₂ ψ₂ hT₁ hT₂
  have := hl₁.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M₁) := leviPointTopology l₁ hl₁
  have : LocallyCompactSpace (rationalPoints M₁) := leviPoints_locallyCompactSpace p₁ l₁ hp₁ hl₁
  have : NonarchimedeanGroup (rationalPoints M₁) := leviPoints_nonarchimedeanGroup p₁ l₁ hp₁ hl₁
  have := hl₂.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M₂) := leviPointTopology l₂ hl₂
  have : LocallyCompactSpace (rationalPoints M₂) := leviPoints_locallyCompactSpace p₂ l₂ hp₂ hl₂
  have : NonarchimedeanGroup (rationalPoints M₂) := leviPoints_nonarchimedeanGroup p₂ l₂ hp₂ hl₂
  intro τ₁ τ₂ π h₁ h₂
  have hirr₁ : τ₁.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ₁.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₁) σ₁).mpr hT₁.2.1
  have hirr₂ : τ₂.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ₂.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₂) σ₂).mpr hT₂.2.1
  -- The embedding of `π` into the opposite induction of the first triplet.
  let O₁ := oppositeLeviParabolic hG p₁ l₁ hp₁ hl₁
  obtain ⟨adj₁⟩ := hAdj k G hG P₁ O₁.parabolic M₁ U₁ O₁.radical p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    O₁.inclusion O₁.levi O₁.unipotent O₁.isParabolic O₁.isLevi O₁.isRadical O₁.multiplication
    O₁.levi_comp O₁.intersection
  have hreg₁ := hK k G hG T i ν D P₁ M₁ U₁ A₁ p₁ l₁ r₁ a₁ hp₁ hl₁ hr₁ hmul₁ ha₁ J₁ f₁ σ₁ ψ₁
    O₁.parabolic O₁.radical O₁.inclusion O₁.levi O₁.unipotent
    O₁.isParabolic O₁.isLevi O₁.isRadical O₁.multiplication O₁.levi_comp O₁.intersection hT₁
  obtain ⟨eS₁⟩ := oppositeIdentitySupport k G hG P₁ M₁ U₁ O₁.parabolic O₁.radical
    p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ O₁.inclusion O₁.levi O₁.unipotent O₁.isParabolic O₁.isLevi
    O₁.isRadical O₁.multiplication O₁.levi_comp O₁.intersection τ₁
  obtain ⟨j₁, hj₁⟩ := exists_regularOppositeQuotientEmbedding p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    O₁.inclusion O₁.levi O₁.unipotent O₁.isParabolic O₁.isLevi O₁.isRadical O₁.multiplication
    hG a₁ ha₁ adj₁ τ₁ hirr₁ hreg₁ eS₁ π h₁
  -- The embedding of `π` into the opposite induction of the second triplet.
  let O₂ := oppositeLeviParabolic hG p₂ l₂ hp₂ hl₂
  obtain ⟨adj₂⟩ := hAdj k G hG P₂ O₂.parabolic M₂ U₂ O₂.radical p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
    O₂.inclusion O₂.levi O₂.unipotent O₂.isParabolic O₂.isLevi O₂.isRadical O₂.multiplication
    O₂.levi_comp O₂.intersection
  have hreg₂ := hK k G hG T i ν D P₂ M₂ U₂ A₂ p₂ l₂ r₂ a₂ hp₂ hl₂ hr₂ hmul₂ ha₂ J₂ f₂ σ₂ ψ₂
    O₂.parabolic O₂.radical O₂.inclusion O₂.levi O₂.unipotent
    O₂.isParabolic O₂.isLevi O₂.isRadical O₂.multiplication O₂.levi_comp O₂.intersection hT₂
  obtain ⟨eS₂⟩ := oppositeIdentitySupport k G hG P₂ M₂ U₂ O₂.parabolic O₂.radical
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ O₂.inclusion O₂.levi O₂.unipotent O₂.isParabolic O₂.isLevi
    O₂.isRadical O₂.multiplication O₂.levi_comp O₂.intersection τ₂
  obtain ⟨j₂, hj₂⟩ := exists_regularOppositeQuotientEmbedding p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
    O₂.inclusion O₂.levi O₂.unipotent O₂.isParabolic O₂.isLevi O₂.isRadical O₂.multiplication
    hG a₂ ha₂ adj₂ τ₂ hirr₂ hreg₂ eS₂ π h₂
  obtain ⟨hπirr, q₁, hq₁⟩ := h₁
  obtain ⟨-, q₂, hq₂⟩ := h₂
  have : Nontrivial π :=
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible π.representation hπirr
  have ht₁ : j₂.comp q₁ ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    obtain ⟨y, rfl⟩ := hq₁ x
    apply hx
    apply hj₂
    have h := congrArg (fun g => g y) hz
    simpa using h
  have ht₂ : j₁.comp q₂ ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    obtain ⟨y, rfl⟩ := hq₂ x
    apply hx
    apply hj₁
    have h := congrArg (fun g => g y) hz
    simpa using h
  exact hR k G hG T i ν D P₁ M₁ U₁ A₁ p₁ l₁ r₁ a₁ hp₁ hl₁ hr₁ hmul₁ ha₁ J₁ f₁ σ₁ ψ₁
    P₂ M₂ U₂ A₂ p₂ l₂ r₂ a₂ hp₂ hl₂ hr₂ hmul₂ ha₂ J₂ f₂ σ₂ ψ₂
    O₁.parabolic O₁.radical O₁.inclusion O₁.levi O₁.unipotent O₁.isParabolic O₁.isLevi
    O₁.isRadical O₁.multiplication
    O₂.parabolic O₂.radical O₂.inclusion O₂.levi O₂.unipotent O₂.isParabolic O₂.isLevi
    O₂.isRadical O₂.multiplication
    O₁.levi_comp O₁.intersection O₂.levi_comp O₂.intersection hT₁ hT₂
    (j₂.comp q₁) ht₁ (j₁.comp q₂) ht₂

end Langlands.Aubert.General.RepresentedParabolic
