import Langlands.AllFieldBZ.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement
import Langlands.AllFieldBZ.Representation.Derivative.ZeroRankTensor
import Langlands.Representation.Derivative.RightMixedProductZeroRank

/-!
# All-field port of `Langlands.Representation.Derivative.RightMixedProductZeroRank`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.RightMixedProductZeroRank` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous RightMixedProductDerivativeFiltrationStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero rightMixedDerivativePiece rightMixedDerivativeSource rightMixedProductDerivativeFiltration_zero
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedProduct
open Langlands.HarmonicAnalysis
open Langlands.Derivative.ZeroRankTensor hiding binaryRightZeroEquiv binaryRightZeroIso generalLinearDerivativePositiveTensorIso generalLinearDerivativeTensorIso generalLinearRankCastTensorIso generalLinearRestrictionTensorIso mirabolicDerivativeOfOrderTensorIso mirabolicDerivativeTensorIso mirabolicRankCastTensorIso phiMinusIterateTensorIso phiMinusTensorIso psiMinusTensorIso
open Langlands.AllFieldBZ.Derivative.ZeroRankTensor
universe uF uV

namespace RightMixedZeroRank
open Langlands.Derivative.RightMixedZeroRank hiding nonempty_sourceIso_piece pieceIso pullbackCastIso rankCastDerivativeIso rightMixedProductZeroEquiv rightMixedProductZeroIso sourceIso
/-! ## One-step filtrations -/

section OneStep
universe uR uG uW uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G] {C : Type uC} [Category.{vC} C]

end OneStep
/-! ## The rank cast `P_(b+1) = P_(a+1)` -/

section RankCast
variable {R : Type*} [CommRing R]

end RankCast
variable {F : LocalFieldPackage.{uF}}

/-- Restriction along the rank cast is the published mirabolic rank transport. -/
def pullbackCastIso (T : F.TopologicalData) {a b : ℕ} (h : a = b)
    (φ : mirabolic b F.Carrier →* mirabolic a F.Carrier)
    (hφ : letI := T.topology; Continuous φ) (heq : φ = castHom h) :
    letI := T.topology
    Mirabolic.continuousPullbackFunctor φ hφ ≅ mirabolicRankCast.{uF, uV} T h := by
  letI := T.topology
  subst h heq
  exact NatIso.ofComponents
    (fun A => SmoothRep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun _ => LinearMap.ext fun _ => rfl))
    fun _ => MixedProductTensor.smoothRep_hom_ext fun _ => rfl

/-- The order-`d` derivative commutes with the mirabolic rank transport. -/
def rankCastDerivativeIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a b : ℕ} (h : a = b) (d : ℕ)
    (ha : 0 < d ∧ d ≤ a + 1) (hb : 0 < d ∧ d ≤ b + 1) (h' : a + 1 - d = b + 1 - d) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ⋙ mirabolicDerivativeOfOrder T ψ b d hb ≅
      mirabolicDerivativeOfOrder T ψ a d ha ⋙ generalLinearRankCast T h' := by
  letI := T.topology
  subst h
  exact Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm

/-! ## The product `B × A` with `A` on `GL_0` -/

/-- `B × A ≃ B ⊗ ULift A` for `A` on `GL_0`: evaluation at `1`, the trivial twist,
and `id ⊗ ULift.up`, with `P_(0+r+1)` acting on `B` through `rightUnitProjection`. -/
def rightMixedProductZeroEquiv (T : F.TopologicalData) (r : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier)) :
    letI := T.topology
    ((T.rightMixedProductFunctor 0 r).obj X).representation.Equiv
      ((tensorFunctor.{uF, uF, uV, max uV uF} (mirabolic (0 + r) F.Carrier)
        (GeneralLinear 0 F.Carrier)).obj
          ((Mirabolic.continuousPullbackFunctor (rightUnitProjection r)
              continuous_rightUnitProjection).obj X.1,
            MixedProductTensor.liftFunctor.{uF, uV, uF}.obj X.2)).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (0 + r + 1)
  (Induction.compactInducedTopEquiv (rightSubgroup 0 r F.Carrier) mem_rightSubgroup_zero _
      ((isSmooth_twist_iff _ _ (T.rightCharacter 0 r).isOpen_ker).mpr
        (isSmooth_rightInducingRepresentation X.1.isSmooth X.2.isSmooth))).trans
    ((MixedProductTensor.compEquiv _
        (MixedProductTensor.twistOneEquiv _ (T.rightCharacter_zero_left r) _)).trans
      (Representation.Equiv.mk
        (TensorProduct.congr (LinearEquiv.refl ℂ X.1) ULift.moduleEquiv.symm)
        fun g => TensorProduct.ext' fun v w => by
          change X.1.representation (rightUnitProjection r g) v ⊗ₜ
              ULift.up (X.2.representation _ w) =
            X.1.representation (rightUnitProjection r g) v ⊗ₜ ULift.up w
          rw [representation_apply_of_rank_eq_zero rfl X.2.representation]
          rfl))

/-- `B × A ≅ B ⊗ ULift A`, naturally in `(B, A)`, when `A` is a representation of `GL_0`. -/
def rightMixedProductZeroIso (T : F.TopologicalData) (r : ℕ) :
    letI := T.topology
    T.rightMixedProductFunctor.{uF, uV} 0 r ≅
      (Mirabolic.continuousPullbackFunctor (rightUnitProjection r)
          continuous_rightUnitProjection).prod MixedProductTensor.liftFunctor.{uF, uV, uF} ⋙
        tensorFunctor.{uF, uF, uV, max uV uF} (mirabolic (0 + r) F.Carrier)
          (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  NatIso.ofComponents (fun X => SmoothRep.mkIso (rightMixedProductZeroEquiv T r X))
    fun {X Y} f => MixedProductTensor.smoothRep_hom_ext fun φ =>
      LinearMap.congr_fun (TensorProduct.ext' fun _ _ => rfl :
        (TensorProduct.congr (LinearEquiv.refl ℂ Y.1) ULift.moduleEquiv.symm).toLinearMap ∘ₗ
            TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap =
          TensorProduct.map (SmoothRep.hom f.1).toLinearMap
              (MixedProductTensor.liftMap (SmoothRep.hom f.2)).toLinearMap ∘ₗ
            (TensorProduct.congr (LinearEquiv.refl ℂ X.1) ULift.moduleEquiv.symm).toLinearMap)
        (T.rightMixedEval X φ 1)

/-! ## Pasting -/

section Pasting
variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W₁ W₂ : Type*} [Category X₁] [Category X₂] [Category Y₁]
  [Category Y₂] [Category Z₁] [Category Z₂] [Category W₁] [Category W₂]

end Pasting
/-! ## Source and grade -/

/-- The derivative of `B × A` is `(B^(d) ⊗ A)` after the rank cast. -/
def sourceIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (r d : ℕ)
    (hd : 0 < d ∧ d ≤ (0 + r) + 1) (hd' : 0 < d ∧ d ≤ r + 1)
    (h' : r + 1 - d = (0 + r) + 1 - d) :
    letI := T.topology
    T.rightMixedProductFunctor.{uF, uV} 0 r ⋙ mirabolicDerivativeOfOrder T ψ (0 + r) d hd ≅
      (mirabolicDerivativeOfOrder T ψ r d hd' ⋙ generalLinearRankCast T h').prod
          MixedProductTensor.liftFunctor.{uF, uV, uF} ⋙
        tensorFunctor.{uF, uF, uV, max uV uF} (GeneralLinear ((0 + r) + 1 - d) F.Carrier)
          (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  sourcePaste (rightMixedProductZeroIso T r)
    (Langlands.AllFieldBZ.Derivative.ZeroRankTensor.mirabolicDerivativeOfOrderTensorIso (GeneralLinear 0 F.Carrier) T ψ (0 + r) d hd)
    (Functor.isoWhiskerRight
        (pullbackCastIso T (Nat.zero_add r).symm (rightUnitProjection r)
          continuous_rightUnitProjection (rightUnitProjection_eq_castHom r))
        (mirabolicDerivativeOfOrder T ψ (0 + r) d hd) ≪≫
      rankCastDerivativeIso T ψ (Nat.zero_add r).symm d hd' hd h')

/-- The `(d, 0)` grade `B^(d) × A^(0)` is `(B^(d) ⊗ A)` after the rank cast. -/
def pieceIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (r d N : ℕ)
    (hd' : 0 < d ∧ d ≤ r + 1) (h0 : 0 ≤ 0) (h : r + 1 - d = N) :
    letI := T.topology
    ((mirabolicDerivativeOfOrder T ψ r d hd').prod (generalLinearDerivative T ψ 0 0 h0) ⋙
        T.binaryNormalizedProductFunctor.{uF, uV} (r + 1 - d) 0) ⋙ generalLinearRankCast T h ≅
      (mirabolicDerivativeOfOrder T ψ r d hd' ⋙ generalLinearRankCast T h).prod
          MixedProductTensor.liftFunctor.{uF, uV, uF} ⋙
        tensorFunctor.{uF, uF, uV, max uV uF} (GeneralLinear N F.Carrier)
          (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  piecePaste (Langlands.AllFieldBZ.Derivative.ZeroRankTensor.binaryRightZeroIso T (r + 1 - d))
    (Langlands.AllFieldBZ.Derivative.ZeroRankTensor.generalLinearRankCastTensorIso (GeneralLinear 0 F.Carrier) T h)
    (Functor.leftUnitor MixedProductTensor.liftFunctor.{uF, uV, uF} :
      generalLinearDerivative T ψ 0 0 h0 ⋙ MixedProductTensor.liftFunctor.{uF, uV, uF} ≅ _)

/-- The source is isomorphic to the unique feasible grade. -/
theorem nonempty_sourceIso_piece (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (r d : ℕ)
    (hd : 0 < d ∧ d ≤ (0 + r) + 1) (x : RightMixedDerivativeIndex 0 r d) :
    letI := T.topology
    Nonempty (rightMixedDerivativeSource.{uF, uV} T ψ 0 r d hd ≅
      rightMixedDerivativePiece T ψ 0 r d x) := by
  let _ := T.topology
  obtain ⟨⟨j, t⟩, hx⟩ := x
  obtain ⟨hj, ht⟩ : j = d ∧ t = 0 := by
    simp only [mem_rightMixedDerivativeIndices] at hx
    omega
  subst j t
  have hd' : 0 < d ∧ d ≤ r + 1 := ⟨hd.1, by omega⟩
  have h' : r + 1 - d = (0 + r) + 1 - d := by omega
  exact ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sourceIso T ψ r d hd hd' h') SmoothRep.toRep ≪≫
    (Functor.isoWhiskerRight (pieceIso T ψ r d _ hd' le_rfl h') SmoothRep.toRep).symm ≪≫
    Functor.associator _ _ _ ≪≫ Functor.associator _ _ _⟩

end RightMixedZeroRank
open Langlands.Derivative.RightMixedZeroRank hiding nonempty_sourceIso_piece pieceIso pullbackCastIso rankCastDerivativeIso rightMixedProductZeroEquiv rightMixedProductZeroIso sourceIso
variable {F : LocalFieldPackage.{uF}}

/-- BZ77 4.14(b) for `k = 0`: the derivative of `B × A`, with `A` on `GL_0`, is glued
from the single feasible grade `B^(d) × A^(0)`. -/
theorem rightMixedProductDerivativeFiltration_zero (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (r d : ℕ)
    (hd : 0 < d ∧ d ≤ (0 + r) + 1) :
    letI := T.topology
    ∃ e : Fin (rightMixedDerivativeIndices 0 r d).card ≃ RightMixedDerivativeIndex 0 r d,
      IsGluedFrom (rightMixedDerivativeSource.{uF, uV} T ψ 0 r d hd)
        (fun i => rightMixedDerivativePiece T ψ 0 r d (e i)) := by
  let _ := T.topology
  have hd' : 0 < d ∧ d ≤ r + 1 := ⟨hd.1, by omega⟩
  refine ⟨(rightMixedDerivativeIndices 0 r d).equivFin.symm, ?_⟩
  refine isGluedFrom_of_iso ?_ fun i => Langlands.AllFieldBZ.Derivative.RightMixedZeroRank.nonempty_sourceIso_piece T ψ r d hd _
  rw [rightMixedDerivativeIndices_zero_gl r d hd', Finset.card_singleton]

end Langlands.AllFieldBZ.Derivative
