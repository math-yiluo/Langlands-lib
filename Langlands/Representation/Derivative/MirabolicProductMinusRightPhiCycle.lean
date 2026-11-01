import Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient
import Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentity

/-!
# The cyclic orbit piece of the right `Φ⁻` sequence

The normalized localized orbit piece of `τ × ρ` at the cyclic representative is
`(Φ⁻τ) × ρ`, naturally in both inputs. The localization of the compact induction
from the stabilizer `S` to the plus subgroup `Q` is the compact induction from
`K = P.comap plusSuccessor` of the localized coefficient (published split-stage
character comparison); `K` is the right mixed subgroup of shape `(k+1, r)` after a rank
cast, and the coefficient with its `Φ⁻` twist and Haar ratio is the normalized right
mixed coefficient of `(Φ⁻τ, ρ)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MeasureTheory MeasureTheory.Measure
open scoped TensorProduct NNReal

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct
  GeneralLinear.Mirabolic.MixedOrbit HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## The rank cast to the right mixed product of shape `(k+1, r)` -/

section Transport

/-- The rank cast `P_(k+r+2) ≅ P_((k+1)+r+1)` as an isomorphism of topological groups. -/
def rightCycleCast (T : F.TopologicalData) (k r : ℕ) :
    letI := T.topology
    mirabolic (k + r + 1) F.Carrier ≃ₜ* mirabolic (k + 1 + r) F.Carrier :=
  letI := T.topology
  { toMulEquiv := (rankCast (R := F.Carrier) (show k + 1 + r = k + r + 1 by omega)).symm
    continuous_toFun := continuous_rankCast_symm _
    continuous_invFun := continuous_rankCast _ }

/-- The published rank-cast pullback is pullback along the same entrywise cast. -/
theorem rightCycleCast_toMonoidHom (T : F.TopologicalData) (k r : ℕ) :
    letI := T.topology
    (rightCycleCast T k r).toMonoidHom =
      mirabolicCastHom (R := F.Carrier) (Nat.succ_add k r) := by
  let := T.topology
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [mirabolicCastHom_apply]
  rfl

/-- The target `(Φ⁻τ) × ρ` with its rank cast replaced by the explicit pullback. -/
abbrev rightCycleTarget (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  (Mirabolic.phiMinus T ψ r).prod (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
    T.rightMixedProductFunctor (k + 1) r ⋙
      Mirabolic.continuousPullbackFunctor (mirabolicCastHom (Nat.succ_add k r))
        (continuous_mirabolicCastHom (Nat.succ_add k r))

/-- Compact induction from `K` of a coefficient identified with the normalized right
mixed coefficient of `(Φ⁻τ, ρ)` is the target, through the rank cast. -/
def rightCycleCompactEquivOf (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
    (κ : Representation ℂ
      ((rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) W)
    (e : letI := T.topology
      W ≃ₗ[ℂ] (Jacquet.Localization.Coinvariants X.1.representation (radical (r + 1) F.Carrier)
        (T.mirabolicTheta ψ r) ⊗[ℂ]
        X.2))
    (he : letI := T.topology; ∀ (l : (rightStages k r F.Carrier 0).comap
        (plusSuccessor (n := k + r + 1) (F := F.Carrier))) (w : W),
      e (κ l w) = ((T.rightCharacter (k + 1) r).toMonoidHom (rightCycleLevi k r F.Carrier l) : ℂ) •
        TensorProduct.map (((Mirabolic.phiMinus T ψ r).obj X.1).representation
            (rightProjection (rightCycleLevi k r F.Carrier l)).1)
          (X.2.representation
            (rightProjection (rightCycleLevi k r F.Carrier l)).2) (e w)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1)
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    (Induction.compactInduced
        ((rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier)))
        κ).Equiv
      ((rightCycleTarget.{uF, uV} T ψ k r).obj X).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1)
  letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  (Induction.compactInducedTransport (rightCycleCast T k r)
      ((rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier)))
      (rightSubgroup (k + 1) r F.Carrier) (mem_rightStages_zero_comap_iff k r F.Carrier) κ
      (twist (T.rightCharacter (k + 1) r).toMonoidHom
        (rightInducingRepresentation ((Mirabolic.phiMinus T ψ r).obj X.1).representation
          X.2.representation)) e he).symm.trans
    (compEquivOfEq _ (rightCycleCast_toMonoidHom T k r))

/-- The identification is natural for a coefficient intertwiner lying over a pair of
morphisms `f = (f₁, f₂)`, i.e. carried to `Φ⁻(f₁) ⊗ f₂`. -/
theorem rightCycleCompactEquivOf_natural (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ)
    {W : Type*} [AddCommGroup W] [Module ℂ W] {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (κ : Representation ℂ
      ((rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) W)
    (e : letI := T.topology
      W ≃ₗ[ℂ] (Jacquet.Localization.Coinvariants X.1.representation (radical (r + 1) F.Carrier)
        (T.mirabolicTheta ψ r) ⊗[ℂ]
        X.2))
    (he : letI := T.topology; ∀ (l : (rightStages k r F.Carrier 0).comap
        (plusSuccessor (n := k + r + 1) (F := F.Carrier))) (w : W),
      e (κ l w) = ((T.rightCharacter (k + 1) r).toMonoidHom (rightCycleLevi k r F.Carrier l) : ℂ) •
        TensorProduct.map (((Mirabolic.phiMinus T ψ r).obj X.1).representation
            (rightProjection (rightCycleLevi k r F.Carrier l)).1)
          (X.2.representation
            (rightProjection (rightCycleLevi k r F.Carrier l)).2) (e w))
    (κ' : Representation ℂ
      ((rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) W')
    (e' : letI := T.topology
      W' ≃ₗ[ℂ] (Jacquet.Localization.Coinvariants Y.1.representation (radical (r + 1) F.Carrier)
        (T.mirabolicTheta ψ r) ⊗[ℂ]
        Y.2))
    (he' : letI := T.topology; ∀ (l : (rightStages k r F.Carrier 0).comap
        (plusSuccessor (n := k + r + 1) (F := F.Carrier))) (w : W'),
      e' (κ' l w) = ((T.rightCharacter (k + 1) r).toMonoidHom (rightCycleLevi k r F.Carrier l) : ℂ) •
        TensorProduct.map (((Mirabolic.phiMinus T ψ r).obj Y.1).representation
            (rightProjection (rightCycleLevi k r F.Carrier l)).1)
          (Y.2.representation
            (rightProjection (rightCycleLevi k r F.Carrier l)).2) (e' w))
    (t : κ.IntertwiningMap κ')
    (ht : letI := T.topology; ∀ w, e' (t w) =
      TensorProduct.map (SmoothRep.hom ((Mirabolic.phiMinus T ψ r).map f.1)).toLinearMap
        (SmoothRep.hom f.2).toLinearMap (e w))
    (u : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + r + 1 + 1)
      Induction.CompactFunctions
        ((rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) κ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1)
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    rightCycleCompactEquivOf T ψ k r Y κ' e' he'
        (Induction.compactInducedMap
          ((rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier)))
          t u) =
      SmoothRep.hom ((rightCycleTarget.{uF, uV} T ψ k r).map f)
        (rightCycleCompactEquivOf T ψ k r X κ e he u) := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup (k + r + 1 + 1)
  let _ := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change e' (t (Induction.eval
      ((rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) κ
      u.val ((rightCycleCast T k r).symm x))) =
    TensorProduct.map (SmoothRep.hom ((Mirabolic.phiMinus T ψ r).map f.1)).toLinearMap
      (SmoothRep.hom f.2).toLinearMap
      (e (Induction.eval
        ((rightStages k r F.Carrier 0).comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))) κ
        u.val ((rightCycleCast T k r).symm x)))
  exact ht _

end Transport

/-! ## The localization of the orbit piece -/

section Localization

variable (T : F.TopologicalData) (k r : ℕ)

/-- The restricted coefficient of the orbit piece, in the form produced by the functors. -/
abbrev rightCycleOrbitCoefficient
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    Representation ℂ (rightCycStabilizer k r F.Carrier)
      ((Rep.resFunctor (Geometric.stabilizerToInducing (G := mirabolic (k + r + 1 + 1) F.Carrier)
          (rightInducing k r F.Carrier)
          (plusSubgroup (k + r + 1) F.Carrier) (rightRepresentative k r F.Carrier 0))).obj
        ((ObjectProperty.ι _).obj ((rightOrbitInput T k r).obj X))) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  ((Rep.resFunctor (Geometric.stabilizerToInducing (G := mirabolic (k + r + 1 + 1) F.Carrier)
      (rightInducing k r F.Carrier)
      (plusSubgroup (k + r + 1) F.Carrier) (rightRepresentative k r F.Carrier 0))).obj
    ((ObjectProperty.ι _).obj ((rightOrbitInput T k r).obj X))).ρ

/-- The functorial form of the orbit coefficient is `χ_R (τ ⊠ ρ)` through the stabilizer. -/
def rightCycleCoefficientBridge
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    (rightCycleOrbitCoefficient T k r X).Equiv
      (rightCycleCoefficient T k r X.1.representation X.2.representation) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun _ => rfl)

/-- The localization of the cyclic orbit piece is the split-kernel localized action of
the orbit piece itself, through the identity. -/
def rightCycleLocalizationEquiv₀
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    Representation.Equiv
      ((Mirabolic.plusPhiLocalization ψ (k + r + 1)).obj
        ((Geometric.orbitPiece (R := ℂ) (G := mirabolic (k + r + 1 + 1) F.Carrier)
          (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
          (rightRepresentative k r F.Carrier 0)).obj ((rightOrbitInput T k r).obj X))).ρ
      (Induction.SplitKernelLocalization.localizedAction
        (plusProjection (n := k + r + 1) (F := F.Carrier)) plusSuccessor
        (plusKernelThetaSmooth T ψ (k + r + 1)).toMonoidHom
        (plusKernelThetaSmooth_sectionInvariant T ψ (k + r + 1))
        ((Geometric.orbitPiece (R := ℂ) (G := mirabolic (k + r + 1 + 1) F.Carrier)
          (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
          (rightRepresentative k r F.Carrier 0)).obj ((rightOrbitInput T k r).obj X)).ρ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  Representation.Equiv.mk (LinearEquiv.refl ℂ _)
    (fun _ => LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun _ => rfl)

/-- The orbit piece is the compact induction of `χ_R (τ ⊠ ρ)` from the stabilizer. -/
def rightCycleOrbitEquiv
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    Representation.Equiv
      ((Geometric.orbitPiece (R := ℂ) (G := mirabolic (k + r + 1 + 1) F.Carrier)
          (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
          (rightRepresentative k r F.Carrier 0)).obj ((rightOrbitInput T k r).obj X)).ρ
      (Induction.compactInduced (rightCycStabilizer k r F.Carrier)
        (rightCycleCoefficient T k r X.1.representation X.2.representation)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  Induction.compactInducedEquiv _ (rightCycleCoefficientBridge T k r X)

end Localization

/-! ## The cyclic orbit piece -/

section Piece

open Induction QuotientIntegration

set_option maxHeartbeats 8000000 in
/-- BZ77 4.13(c), open orbit: the normalized localized orbit piece of `τ × ρ` at the
cyclic representative is `(Φ⁻τ) × ρ`, naturally in `(τ, ρ)`. -/
theorem rightPhiCyclePiece_iso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    Nonempty (rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 0) ≅
      rightPhiSubobject.{uF, uV} T ψ k r ⋙
        SmoothRep.toRep (G := mirabolic (k + r + 1) F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  let := T.generalLinearTopologicalGroup (k + r + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (k + r + 1 + 1 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := k + r + 1 + 1) (F := F.Carrier)
  let : LocallyCompactSpace (plusSubgroup (k + r + 1) F.Carrier) :=
    plusSubgroup_isClosed.locallyCompactSpace
  have := isTopologicalRing_of_topologicalData F T
  -- The split-stage data on `Q = P_(k+r+2) V_(k+r+3)`.
  let P := rightStages k r F.Carrier 0
  let S := rightCycStabilizer k r F.Carrier
  let K := P.comap (plusSuccessor (n := k + r + 1) (F := F.Carrier))
  have hker : (plusProjection (n := k + r + 1) (F := F.Carrier)).ker ≤ P :=
    plusKernel_le_stagesSubgroup _ _
  have hHP : S ≤ P := rightCycStabilizer_le_stages k r F.Carrier
  have hP : IsClosed (P : Set (plusSubgroup (k + r + 1) F.Carrier)) :=
    rightStages_isClosed k r F.Carrier 0
  have hH : IsClosed (S : Set (plusSubgroup (k + r + 1) F.Carrier)) :=
    rightCycStabilizer_isClosed k r F.Carrier
  have hsH := rightCycle_section_mem k r F.Carrier
  have hr : Continuous (plusProjection (n := k + r + 1) (F := F.Carrier)) :=
    continuous_plusProjection
  have hs : Continuous (plusSuccessor (n := k + r + 1) (F := F.Carrier)) :=
    continuous_plusSuccessor
  let θ := plusKernelThetaSmooth T ψ (k + r + 1)
  have hθ := plusKernelThetaSmooth_sectionInvariant T ψ (k + r + 1)
  have hN : IsClosed ((plusProjection (n := k + r + 1) (F := F.Carrier)).ker :
      Set (plusSubgroup (k + r + 1) F.Carrier)) :=
    isClosed_singleton.preimage continuous_plusProjection
  have hBasis := plusSubgroup_compactOpenBasis T (k + r + 1)
  -- Measures on the kernel, its intersection with the stabilizer and the quotient.
  let rP := rightCycleRetraction k r F.Carrier
  let eK := splitStagesKernelContinuousEquiv plusProjection plusSuccessor
    plusProjection_plusSuccessor P hker
  let : LocallyCompactSpace (plusProjection (n := k + r + 1) (F := F.Carrier)).ker :=
    hN.locallyCompactSpace
  let : LocallyCompactSpace rP.ker := eK.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hIc : IsClosed (((rightCycleInducing k r F.Carrier).comap rP.ker.subtype :
      Subgroup rP.ker) : Set rP.ker) :=
    isClosed_splitKernelIntersection _ _ (hH.preimage continuous_subtype_val)
  let : LocallyCompactSpace ((rightCycleInducing k r F.Carrier).comap rP.ker.subtype) :=
    hIc.locallyCompactSpace
  let : MeasurableSpace rP.ker := borel _
  have : BorelSpace rP.ker := ⟨rfl⟩
  let : MeasurableSpace ((rightCycleInducing k r F.Carrier).comap rP.ker.subtype) := borel _
  have : BorelSpace ((rightCycleInducing k r F.Carrier).comap rP.ker.subtype) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    ((rightCycleInducing k r F.Carrier).comap rP.ker.subtype)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient
    ((rightCycleInducing k r F.Carrier).comap rP.ker.subtype)) := ⟨rfl⟩
  let eR : rP.ker ≃ₜ* radical (k + r + 1 + 1) F.Carrier :=
    eK.trans (plusKernelContinuousEquiv F.Carrier)
  have hKernelBasis := compactOpenBasis_of_continuousMulEquiv eR
    (radical_compactOpenBasis T (k + r + 1))
  have hCover := compactOpenCover_of_continuousMulEquiv eR
    (radical_compactOpenCover T (k + r + 1))
  have hu := Haar.compactOpenCoverUnimodularity hCover
  let μN : Measure rP.ker := haar
  let μI : Measure ((rightCycleInducing k r F.Carrier).comap rP.ker.subtype) := haar
  have : IsMulRightInvariant μN := hu.1 μN
  have : IsMulRightInvariant μI := hu.2 _ hIc μI
  obtain ⟨ν, hν⟩ := QuotientIntegration.compatibleMeasureExists _ hIc μN μI
  have : ν.Regular := hν.regular
  -- The coefficient `χ_R (τ ⊠ ρ)` on the stabilizer is smooth.
  have hσ : ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier),
      IsSmooth (rightCycleCoefficient T k r X.1.representation X.2.representation) :=
    fun X => isSmooth_comp (rightCycleInclusion k r F.Carrier)
      ((continuous_rightInducingHom k r F.Carrier).comp (continuous_stabilizerToInducing _ _))
      ((isSmooth_twist_iff _ _ (T.rightCharacter (k + 1) (r + 1)).isOpen_ker).mpr
        (isSmooth_rightInducingRepresentation X.1.isSmooth X.2.isSmooth))
  -- The localized coefficient and its character, `θ_r` on the kernel intersection.
  let η := SplitKernelLocalization.intersectionCharacter rP
    (SplitStagesCharacter.kernelCharacter plusProjection plusSuccessor plusProjection_plusSuccessor
      P hker θ).toMonoidHom (rightCycleInducing k r F.Carrier)
  have hη : ∀ a, η a = T.mirabolicTheta ψ r (rightPsiKernelEquiv
      (rightCycleKernelEquiv k r F.Carrier (rightCycleIntersectionToKernel k r F.Carrier a))) :=
    fun a =>
    thetaPlus_rightCycle k r F.Carrier ψ (rightCycleIntersectionToKernel k r F.Carrier a)
  let κ := fun X : SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) =>
    SplitStagesCharacter.coefficientAction plusProjection plusSuccessor
      plusProjection_plusSuccessor P S hker hHP hH hsH θ hθ
      (rightCycleCoefficient T k r X.1.representation X.2.representation)
  let φc : SmoothCharacter ℂ (mirabolic (k + r + 1) F.Carrier) :=
    ⟨Mirabolic.phiMinusCharacter T (k + r + 1), Mirabolic.isOpen_ker_phiMinusCharacter T (k + r + 1)⟩
  -- The normalized coefficient is the normalized right mixed coefficient of `(Φ⁻τ, ρ)`.
  have hE : ∀ (X : SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) (l : K)
      (w : Jacquet.Localization.Coinvariants
        (rightCycleStagesCoefficient T k r X.1.representation X.2.representation)
        (rightCycleKernelIntersection k r F.Carrier) η),
      rightCycleCoefficientEquiv T ψ k r X.1.representation X.2.representation η hη
          (twist (φc.toMonoidHom.comp K.subtype) (κ X) l w) =
        ((T.rightCharacter (k + 1) r).toMonoidHom (rightCycleLevi k r F.Carrier l) : ℂ) •
          TensorProduct.map (((Mirabolic.phiMinus T ψ r).obj X.1).representation
              (rightProjection (rightCycleLevi k r F.Carrier l)).1)
            (X.2.representation
              (rightProjection (rightCycleLevi k r F.Carrier l)).2)
            (rightCycleCoefficientEquiv T ψ k r X.1.representation X.2.representation η hη w) := by
    intro X l w
    refine localization_tensor_ext_smul
      (rightCycleCoefficientEquiv T ψ k r X.1.representation X.2.representation η hη)
      (twist (φc.toMonoidHom.comp K.subtype) (κ X) l) _ _ (fun a b => ?_) w
    have h₁ : twist (φc.toMonoidHom.comp K.subtype) (κ X) l
        (Jacquet.Localization.mk
          (rightCycleStagesCoefficient T k r X.1.representation X.2.representation)
          (rightCycleKernelIntersection k r F.Carrier) η (a ⊗ₜ b)) =
        (((φc.toMonoidHom.comp K.subtype) l : ℂ) *
          (SplitStagesCharacter.haarCharacter plusProjection plusSuccessor
            plusProjection_plusSuccessor P S hker hH hsH l : ℂ)) •
          Jacquet.Localization.mk
            (rightCycleStagesCoefficient T k r X.1.representation X.2.representation)
            (rightCycleKernelIntersection k r F.Carrier) η
            (rightCycleStagesCoefficient T k r X.1.representation X.2.representation
              (SplitKernelLocalization.subgroupSection
                ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap P)
                (rightCycleInducing k r F.Carrier)
                (rightCycleInducing_section_mem k r F.Carrier) l) (a ⊗ₜ b)) := by
      change ((φc.toMonoidHom.comp K.subtype) l : ℂ) • (κ X) l (Jacquet.Localization.mk
          (rightCycleStagesCoefficient T k r X.1.representation X.2.representation)
          (rightCycleKernelIntersection k r F.Carrier) η (a ⊗ₜ b)) = _
      rw [SplitStagesCharacter.coefficientAction_mk, smul_smul]
    exact linearEquiv_smul_chain _ h₁
      (rightCycleCoefficientEquiv_section T ψ k r _ _ η hη l a b)
      (rightCycle_phiMinus_tmul T ψ k r X.1 X.2 _ _ a b) (rightCycle_scalar_eq T k r l)
  -- The chain of identifications.
  let E : ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier),
      Representation.Equiv
        ((rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 0)).obj X).ρ
        ((rightCycleTarget.{uF, uV} T ψ k r).obj X).representation := fun X =>
    (twistEquiv (Mirabolic.phiMinusCharacter T (k + r + 1))
      ((rightCycleLocalizationEquiv₀ T k r ψ X).trans
        ((localizedActionEquiv plusProjection plusSuccessor θ.toMonoidHom hθ
          (rightCycleOrbitEquiv T k r X)).trans
          (SplitStagesCharacter.comparisonEquiv plusProjection plusSuccessor
            plusProjection_plusSuccessor hr hs P S hker hHP hP hH hsH θ hθ
            (rightCycleCoefficient T k r X.1.representation X.2.representation) (hσ X)
            ν hKernelBasis μN μI hν hN hBasis)))).trans
    ((compactInductionTwistEquiv K φc (κ X)).trans
      (rightCycleCompactEquivOf T ψ k r X (twist (φc.toMonoidHom.comp K.subtype) (κ X))
        (rightCycleCoefficientEquiv T ψ k r X.1.representation X.2.representation η hη)
        (hE X)))
  -- Each step of the chain is natural.
  have hEnat : ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)} (φ : X ⟶ Y)
      (x : (rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 0)).obj X),
      E Y (((rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 0)).map φ).hom x) =
        SmoothRep.hom ((rightCycleTarget.{uF, uV} T ψ k r).map φ) (E X x) := by
    intro X Y φ x
    let orbitMap := ((Geometric.orbitPiece (R := ℂ) (G := mirabolic (k + r + 1 + 1) F.Carrier)
      (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
      (rightRepresentative k r F.Carrier 0)).map ((rightOrbitInput T k r).map φ)).hom
    let tR := Induction.restrictAlongMap (rightCycleInclusion k r F.Carrier)
      (twistIntertwining (T.rightCharacter (k + 1) (r + 1)).toMonoidHom
        (MixedProductTensor.pullbackMap rightProjection
          (MixedProductTensor.externalMap (SmoothRep.hom φ.1) (SmoothRep.hom φ.2))))
    let cK := twistIntertwining (SplitStagesCharacter.haarCharacter plusProjection plusSuccessor
        plusProjection_plusSuccessor P S hker hH hsH)
      (SplitKernelLocalization.subgroupMap rP
        ((plusSuccessor (n := k + r + 1) (F := F.Carrier)).subgroupComap P)
        (SplitStagesCharacter.kernelCharacter plusProjection plusSuccessor
          plusProjection_plusSuccessor P hker θ).toMonoidHom
        (SplitStagesCharacter.sectionInvariant plusProjection plusSuccessor
          plusProjection_plusSuccessor P hker θ hθ)
        (rightCycleInducing k r F.Carrier)
        (SplitStagesCharacter.section_mem plusSuccessor P S hsH)
        (Induction.restrictAlongMap (Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom tR))
    have h0 : rightCycleLocalizationEquiv₀ T k r ψ Y
        (((Mirabolic.plusPhiLocalization ψ (k + r + 1)).map
          ((Geometric.orbitPiece (R := ℂ) (G := mirabolic (k + r + 1 + 1) F.Carrier)
            (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
            (rightRepresentative k r F.Carrier 0)).map ((rightOrbitInput T k r).map φ))).hom x) =
        SplitKernelLocalization.sectionMap plusProjection plusSuccessor θ.toMonoidHom hθ orbitMap
          (rightCycleLocalizationEquiv₀ T k r ψ X x) :=
      Submodule.Quotient.induction_on _ x fun _ => rfl
    have horb : ∀ v, rightCycleOrbitEquiv T k r Y (orbitMap v) =
        Induction.compactInducedMap S tR (rightCycleOrbitEquiv T k r X v) := by
      intro v
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have h1 := localizedActionEquiv_natural plusProjection plusSuccessor θ.toMonoidHom hθ
      (rightCycleOrbitEquiv T k r X) (rightCycleOrbitEquiv T k r Y) orbitMap
      (Induction.compactInducedMap S tR) horb (rightCycleLocalizationEquiv₀ T k r ψ X x)
    have h2 := SplitStagesCharacter.comparisonEquiv_natural plusProjection plusSuccessor
      plusProjection_plusSuccessor hr hs P S hker hHP hP hH hsH θ hθ
      (rightCycleCoefficient T k r X.1.representation X.2.representation) (hσ X)
      ν hKernelBasis μN μI hν hN hBasis (hσ Y) tR
      (localizedActionEquiv plusProjection plusSuccessor θ.toMonoidHom hθ
        (rightCycleOrbitEquiv T k r X) (rightCycleLocalizationEquiv₀ T k r ψ X x))
    have h3 := compactInductionTwistEquiv_natural K φc cK
      (SplitStagesCharacter.comparisonEquiv plusProjection plusSuccessor
        plusProjection_plusSuccessor hr hs P S hker hHP hP hH hsH θ hθ
        (rightCycleCoefficient T k r X.1.representation X.2.representation) (hσ X)
        ν hKernelBasis μN μI hν hN hBasis
        (localizedActionEquiv plusProjection plusSuccessor θ.toMonoidHom hθ
          (rightCycleOrbitEquiv T k r X) (rightCycleLocalizationEquiv₀ T k r ψ X x)))
    have ht : ∀ w : Jacquet.Localization.Coinvariants
        (rightCycleStagesCoefficient T k r X.1.representation X.2.representation)
        (rightCycleKernelIntersection k r F.Carrier) η,
        rightCycleCoefficientEquiv T ψ k r Y.1.representation Y.2.representation η hη (cK w) =
        TensorProduct.map (SmoothRep.hom ((Mirabolic.phiMinus T ψ r).map φ.1)).toLinearMap
          (SmoothRep.hom φ.2).toLinearMap
          (rightCycleCoefficientEquiv T ψ k r X.1.representation X.2.representation η hη w) := by
      intro w
      obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
        (rightCycleStagesCoefficient T k r X.1.representation X.2.representation)
        (rightCycleKernelIntersection k r F.Carrier) η w
      exact rightCycleCoefficientEquiv_natural T ψ k r φ.1 φ.2 tR.toLinearMap (fun _ _ => rfl)
        η hη v
    have h4 := rightCycleCompactEquivOf_natural T ψ k r φ
      (twist (φc.toMonoidHom.comp K.subtype) (κ X))
      (rightCycleCoefficientEquiv T ψ k r X.1.representation X.2.representation η hη) (hE X)
      (twist (φc.toMonoidHom.comp K.subtype) (κ Y))
      (rightCycleCoefficientEquiv T ψ k r Y.1.representation Y.2.representation η hη) (hE Y)
      (twistIntertwining (φc.toMonoidHom.comp K.subtype) cK) ht
      (compactInductionTwistEquiv K φc (κ X)
        (SplitStagesCharacter.comparisonEquiv plusProjection plusSuccessor
          plusProjection_plusSuccessor hr hs P S hker hHP hP hH hsH θ hθ
          (rightCycleCoefficient T k r X.1.representation X.2.representation) (hσ X)
          ν hKernelBasis μN μI hν hN hBasis
          (localizedActionEquiv plusProjection plusSuccessor θ.toMonoidHom hθ
            (rightCycleOrbitEquiv T k r X) (rightCycleLocalizationEquiv₀ T k r ψ X x))))
    exact chain_natural₅ x h0 h1 h2 h3 h4
  -- Assemble the natural isomorphism.
  let iso0 : rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 0) ≅
      rightCycleTarget.{uF, uV} T ψ k r ⋙ SmoothRep.toRep (G := mirabolic (k + r + 1) F.Carrier) :=
    NatIso.ofComponents (fun X => Rep.mkIso (E X)) (by
      intro X Y φ
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact hEnat φ x)
  exact ⟨iso0 ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerLeft
    ((Mirabolic.phiMinus T ψ r).prod (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
      T.rightMixedProductFunctor (k + 1) r)
    (mirabolicRankCastIso.{uF, max uF uV} T (Nat.succ_add k r)).symm) SmoothRep.toRep⟩

end Piece

end Langlands.Derivative.MirabolicProductMinus
