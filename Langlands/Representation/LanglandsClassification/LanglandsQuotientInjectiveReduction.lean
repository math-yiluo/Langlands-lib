import Langlands.Representation.LanglandsClassification.LanglandsClassificationStatement
import Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityReduction
import Langlands.Representation.LanglandsClassification.RegularOppositeLanglandsHead
import Langlands.Representation.LanglandsClassification.OppositeLeviParabolic
import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement
import Langlands.Representation.Intertwining.OppositeIdentitySupportProof

/-! # Langlands quotient injectivity from opposite intertwining rigidity

Renard VII.4.2 (ii) passes through the diagram (VII.4.2.1): a common irreducible
quotient `π` of `i_{P₁}^G(σ₁ ψ₁)` and `i_{P₂}^G(σ₂ ψ₂)` embeds into the opposite
induction `i_{P̄₂}^G(σ₂ ψ₂)`, so the composite gives a nonzero intertwiner
`i_{P₁}^G(σ₁ ψ₁) → i_{P̄₂}^G(σ₂ ψ₂)`. The rest of the proof uses only this nonzero
intertwiner. That remaining assertion is the proposition
`LanglandsTripletOppositeIntertwiningRigidityStatement`; the theorem
`langlandsQuotientInjective_of_inputs` derives the exact part (ii) from it, second
adjointness and the opposite kernel part of VII.4.1.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The part of the proof of Renard VII.4.2 (ii) after the diagram (VII.4.2.1): for two
Langlands triplets `(P₁ = M₁N₁, σ₁, ψ₁)` and `(P₂ = M₂N₂, σ₂, ψ₂)` relative to the same
choices, and any actual parabolic `Q₂` opposite to `P₂` with the same Levi `M₂`, a nonzero
intertwining map `i_{P₁}^G(σ₁ ⊗ ψ₁) → i_{Q₂}^G(σ₂ ⊗ ψ₂)` forces `M₁ = M₂` (equal simple-root
indices), equal norms `|ψ₁| = |ψ₂|` on the common Levi points and `σ₁ ⊗ ψ₁ ≅ σ₂ ⊗ ψ₂` over the
common Levi points; the conclusion is literally that of `LanglandsQuotientInjectiveStatement`. -/
def LanglandsTripletOppositeIntertwiningRigidityStatement : Prop :=
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
      (P₂ M₂ : GroupScheme (Spec (CommRingCat.of k)))
      (A₂ : CommGroupScheme (Spec (CommRingCat.of k)))
      (p₂ : P₂ ⟶ G) (l₂ : M₂ ⟶ P₂) (a₂ : A₂.toGrp ⟶ M₂)
      (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
      (ha₂ : IsSplitComponent a₂)
      (J₂ : Set (characterLattice T)) (f₂ : A₂ ⟶ T)
      (σ₂ : letI := leviPointTopology l₂ hl₂; SmoothRep.{0, u, v} ℂ (rationalPoints M₂))
      (ψ₂ : leviUnramifiedCharacters l₂ hl₂)
      (Q₂ V₂ : GroupScheme (Spec (CommRingCat.of k)))
      (q₂ : Q₂ ⟶ G) (lQ₂ : M₂ ⟶ Q₂) (rQ₂ : V₂ ⟶ Q₂)
      (hq₂ : IsParabolicSubgroup q₂) (hlQ₂ : IsRationalLeviSubgroup lQ₂)
      (hrQ₂ : LeviSubgroup.IsGeometricUnipotentRadical rQ₂)
      (hmulQ₂ : IsIso (subgroupMultiplication lQ₂ rQ₂)),
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
        ∀ t : ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj τ₁).representation.IntertwiningMap
            ((leviInductionFunctor q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂).obj τ₂).representation,
          t ≠ 0 →
            J₁ = J₂ ∧
            (∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
              rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
                ‖(ψ₁.val m₁ : ℂ)‖ = ‖(ψ₂.val m₂ : ℂ)‖) ∧
            ∃ φ : τ₁ ≃ₗ[ℂ] τ₂,
              ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
                rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
                  ∀ x : τ₁, φ (τ₁.representation m₁ x) = τ₂.representation m₂ (φ x)

/-- Renard VII.4.2 (ii) from second adjointness, the opposite kernel part of VII.4.1 and
opposite intertwining rigidity. A common irreducible quotient embeds into the opposite
induction of the second triplet; composing with the first quotient map gives a nonzero
intertwiner, to which rigidity applies. Opposite identity support is the proved
`oppositeIdentitySupport`. -/
theorem langlandsQuotientInjective_of_inputs
    (hAdj : LeviSecondAdjointnessStatement.{u, v})
    (hK : LanglandsTripletOppositeKernelStatement.{u, v})
    (hR : LanglandsTripletOppositeIntertwiningRigidityStatement.{u, v}) :
    LanglandsQuotientInjectiveStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D P₁ M₁ U₁ A₁ p₁ l₁ r₁ a₁ hp₁ hl₁ hr₁ hmul₁ ha₁ J₁ f₁ σ₁ ψ₁
    P₂ M₂ U₂ A₂ p₂ l₂ r₂ a₂ hp₂ hl₂ hr₂ hmul₂ ha₂ J₂ f₂ σ₂ ψ₂ hT₁ hT₂
  let : TopologicalSpace (rationalPoints M₁) := leviPointTopology l₁ hl₁
  have : NonarchimedeanGroup (rationalPoints M₁) := leviPoints_nonarchimedeanGroup p₁ l₁ hp₁ hl₁
  have := hl₂.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M₂) := leviPointTopology l₂ hl₂
  have : LocallyCompactSpace (rationalPoints M₂) := leviPoints_locallyCompactSpace p₂ l₂ hp₂ hl₂
  have : NonarchimedeanGroup (rationalPoints M₂) := leviPoints_nonarchimedeanGroup p₂ l₂ hp₂ hl₂
  intro τ₁ τ₂ π h₁ h₂
  have hirr₂ : τ₂.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ₂.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₂) σ₂).mpr hT₂.2.1
  let O := oppositeLeviParabolic hG p₂ l₂ hp₂ hl₂
  obtain ⟨adj⟩ := hAdj k G hG P₂ O.parabolic M₂ U₂ O.radical p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
    O.inclusion O.levi O.unipotent O.isParabolic O.isLevi O.isRadical O.multiplication
    O.levi_comp O.intersection
  have hreg := hK k G hG T i ν D P₂ M₂ U₂ A₂ p₂ l₂ r₂ a₂ hp₂ hl₂ hr₂ hmul₂ ha₂ J₂ f₂ σ₂ ψ₂
    O.parabolic O.radical O.inclusion O.levi O.unipotent
    O.isParabolic O.isLevi O.isRadical O.multiplication O.levi_comp O.intersection hT₂
  obtain ⟨eS⟩ := oppositeIdentitySupport k G hG P₂ M₂ U₂ O.parabolic O.radical
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ O.inclusion O.levi O.unipotent O.isParabolic O.isLevi
    O.isRadical O.multiplication O.levi_comp O.intersection τ₂
  obtain ⟨j, hj⟩ := exists_regularOppositeQuotientEmbedding p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
    O.inclusion O.levi O.unipotent O.isParabolic O.isLevi O.isRadical O.multiplication
    hG a₂ ha₂ adj τ₂ hirr₂ hreg eS π h₂
  obtain ⟨hπirr, q, hq⟩ := h₁
  have : Nontrivial π :=
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible π.representation hπirr
  have ht : j.comp q ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    obtain ⟨y, rfl⟩ := hq x
    apply hx
    apply hj
    have h := congrArg (fun g => g y) hz
    simpa using h
  exact hR k G hG T i ν D P₁ M₁ U₁ A₁ p₁ l₁ r₁ a₁ hp₁ hl₁ hr₁ hmul₁ ha₁ J₁ f₁ σ₁ ψ₁
    P₂ M₂ A₂ p₂ l₂ a₂ hp₂ hl₂ ha₂ J₂ f₂ σ₂ ψ₂
    O.parabolic O.radical O.inclusion O.levi O.unipotent O.isParabolic O.isLevi O.isRadical
    O.multiplication O.levi_comp O.intersection hT₁ hT₂ (j.comp q) ht

end Langlands.Aubert.General.RepresentedParabolic
