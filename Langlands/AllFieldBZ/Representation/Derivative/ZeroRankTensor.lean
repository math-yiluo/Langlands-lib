import Langlands.AllFieldBZ.Representation.Derivative.Homogeneity
import Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Derivative.ZeroRankTensor

/-!
# All-field port of `Langlands.Representation.Derivative.ZeroRankTensor`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.ZeroRankTensor` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace Langlands.AllFieldBZ.Derivative.ZeroRankTensor
open Langlands.Derivative.ZeroRankTensor hiding binaryRightZeroEquiv binaryRightZeroIso generalLinearDerivativePositiveTensorIso generalLinearDerivativeTensorIso generalLinearRankCastTensorIso generalLinearRestrictionTensorIso mirabolicDerivativeOfOrderTensorIso mirabolicDerivativeTensorIso mirabolicRankCastTensorIso phiMinusIterateTensorIso phiMinusTensorIso psiMinusTensorIso
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedProduct
open Langlands.HarmonicAnalysis
universe uF uG uH uK uV uW

/-! ## Localization of the first tensor factor -/

section Coinvariants
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Coinvariants
/-! ## Tensoring with an inert factor -/

section TensorFunctor
variable (G : Type uG) [Group G] [TopologicalSpace G]
variable (K : Type uK) [Group K] [TopologicalSpace K]

end TensorFunctor
/-! ## Localization functors commute with the inert tensor factor -/

section Localization
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {H : Type uH} [Group H] [TopologicalSpace H]
variable {K : Type uK} [Group K] [TopologicalSpace K]
variable (U : Subgroup G) (θ : U →* ℂˣ) (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
  (hθ : Jacquet.Localization.IsInvariant U M hMU θ) (e : H →* M) (he : Continuous e)
  (χ : H →* ℂˣ) (hχ : IsOpen (χ.ker : Set H))

end Localization
/-! ## Pasting commutation squares -/

section Pasting
variable {A₁ A₂ A₃ B C₁ C₂ C₃ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category B]
  [Category C₁] [Category C₂] [Category C₃]

end Pasting
/-! ## Minus functors and derivatives -/

section Derivatives
variable {F : LocalFieldPackage.{uF}}
variable (K : Type uK) [Group K] [TopologicalSpace K]

/-- `Φ⁻(X ⊗ A) ≅ Φ⁻(X) ⊗ A`, naturally in `(X, A)`. -/
def phiMinusTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (mirabolic (n + 1) F.Carrier) K ⋙ Mirabolic.phiMinus T ψ n ≅
      (Mirabolic.phiMinus T ψ n).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (mirabolic n F.Carrier) K := by
  letI := T.topology
  exact localizationTensorIso (radical (n + 1) F.Carrier) (T.mirabolicTheta ψ n)
    (successorSubgroup n F.Carrier) successorSubgroup_le_normalizer
    (Langlands.Derivative.Mirabolic.theta_isInvariant ψ n)
    (successorContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
    (successorContinuousEquiv (n := n) (F := F.Carrier)).continuous
    (Mirabolic.phiMinusCharacter T n) (Mirabolic.isOpen_ker_phiMinusCharacter T n)

/-- `Ψ⁻(X ⊗ A) ≅ Ψ⁻(X) ⊗ A`, naturally in `(X, A)`. -/
def psiMinusTensorIso (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (mirabolic n F.Carrier) K ⋙ Mirabolic.psiMinus T n ≅
      (Mirabolic.psiMinus T n).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (GeneralLinear n F.Carrier) K := by
  letI := T.topology
  exact localizationTensorIso (radical n F.Carrier) 1 (leviSubgroup n F.Carrier)
    leviSubgroup_le_normalizer
    (Jacquet.Localization.isInvariant_one _ _ leviSubgroup_le_normalizer)
    (leviContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
    (leviContinuousEquiv (n := n) (F := F.Carrier)).continuous
    (Mirabolic.psiMinusCharacter T n) (Mirabolic.isOpen_ker_psiMinusCharacter T n)

/-- `(Φ⁻)^k(X ⊗ A) ≅ (Φ⁻)^k(X) ⊗ A`. -/
def phiMinusIterateTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    (k : ℕ) →
      letI := T.topology
      tensorFunctor.{uF, uK, uV, uW} (mirabolic (n + k) F.Carrier) K ⋙
          phiMinusIterate T ψ n k ≅
        (phiMinusIterate T ψ n k).prod (𝟭 _) ⋙
          tensorFunctor.{uF, uK, uV, uW} (mirabolic n F.Carrier) K
  | 0 => letI := T.topology; Iso.refl _
  | k + 1 => letI := T.topology
      prodCommIsoComp (phiMinusTensorIso K T ψ (n + k)) (phiMinusIterateTensorIso T ψ n k)

/-- The mirabolic derivative `Ψ⁻ ∘ (Φ⁻)^k` commutes with the inert tensor factor. -/
def mirabolicDerivativeTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (mirabolic (n + k) F.Carrier) K ⋙
        mirabolicDerivative T ψ n k ≅
      (mirabolicDerivative T ψ n k).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (GeneralLinear n F.Carrier) K :=
  letI := T.topology
  prodCommIsoComp (phiMinusIterateTensorIso K T ψ n k) (psiMinusTensorIso K T n)

/-- The mirabolic rank transport commutes with the inert tensor factor. -/
def mirabolicRankCastTensorIso (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (mirabolic a F.Carrier) K ⋙ mirabolicRankCast T h ≅
      (mirabolicRankCast T h).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (mirabolic b F.Carrier) K := by
  letI := T.topology
  subst h
  exact Iso.refl _

/-- The order-indexed mirabolic derivative commutes with the inert tensor factor. -/
def mirabolicDerivativeOfOrderTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ)
    (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (mirabolic N F.Carrier) K ⋙
        mirabolicDerivativeOfOrder T ψ N k hk ≅
      (mirabolicDerivativeOfOrder T ψ N k hk).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (GeneralLinear (N + 1 - k) F.Carrier) K :=
  letI := T.topology
  prodCommIsoComp (mirabolicRankCastTensorIso K T (Langlands.Derivative.mirabolic_rank_eq_of_order hk))
    (mirabolicDerivativeTensorIso K T ψ (N + 1 - k) (k - 1))

/-- The `GL` rank transport commutes with the inert tensor factor. -/
def generalLinearRankCastTensorIso (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (GeneralLinear a F.Carrier) K ⋙ generalLinearRankCast T h ≅
      (generalLinearRankCast T h).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (GeneralLinear b F.Carrier) K := by
  letI := T.topology
  subst h
  exact Iso.refl _

/-- Restriction from `GL_(n+1)` to `P_(n+1)` commutes with the inert tensor factor. -/
def generalLinearRestrictionTensorIso (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (GeneralLinear (n + 1) F.Carrier) K ⋙
        generalLinearRestriction T n ≅
      (generalLinearRestriction T n).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (mirabolic n F.Carrier) K := by
  letI := T.topology
  exact pullbackTensorIso K (mirabolic n F.Carrier).subtype continuous_subtype_val

/-- The positive-order `GL` derivative commutes with the inert tensor factor. -/
def generalLinearDerivativePositiveTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    tensorFunctor.{uF, uK, uV, uW} (GeneralLinear (n + k + 1) F.Carrier) K ⋙
        generalLinearDerivativePositive T ψ n k ≅
      (generalLinearDerivativePositive T ψ n k).prod (𝟭 _) ⋙
        tensorFunctor.{uF, uK, uV, uW} (GeneralLinear n F.Carrier) K :=
  letI := T.topology
  prodCommIsoComp (generalLinearRestrictionTensorIso K T (n + k))
    (mirabolicDerivativeTensorIso K T ψ n k)

/-- The `k`-th `GL` derivative commutes with the inert tensor factor. -/
def generalLinearDerivativeTensorIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ) :
    (k : ℕ) → (hk : k ≤ N) →
      letI := T.topology
      tensorFunctor.{uF, uK, uV, uW} (GeneralLinear N F.Carrier) K ⋙
          generalLinearDerivative T ψ N k hk ≅
        (generalLinearDerivative T ψ N k hk).prod (𝟭 _) ⋙
          tensorFunctor.{uF, uK, uV, uW} (GeneralLinear (N - k) F.Carrier) K
  | 0, _ => letI := T.topology; Iso.refl _
  | k + 1, hk => letI := T.topology
      prodCommIsoComp (generalLinearRankCastTensorIso K T (Langlands.Derivative.rank_eq_of_succ_le hk))
        (generalLinearDerivativePositiveTensorIso K T ψ (N - (k + 1)) k)

end Derivatives
/-! ## The binary product with a `GL_0` factor -/

section BinaryZero
variable {F : LocalFieldPackage.{uF}}

/-- `A × B ≃ A ⊗ ULift B` for a representation `B` of `GL_0`: the published `b = 0`
model followed by `ULift.up` on the second factor. -/
def binaryRightZeroEquiv (T : F.TopologicalData) (a : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor a 0).obj X).representation.Equiv
      ((tensorFunctor.{uF, uF, uV, max uV uF} (GeneralLinear a F.Carrier)
        (GeneralLinear 0 F.Carrier)).obj
          (X.1, MixedProductTensor.liftFunctor.{uF, uV, uF}.obj X.2)).representation :=
  letI := T.topology
  (T.binaryRightZeroTensorEquiv rfl X).trans
    (Representation.Equiv.mk
      (TensorProduct.congr (LinearEquiv.refl ℂ X.1) ULift.moduleEquiv.symm)
      fun g => TensorProduct.ext' fun v w => by
        change X.1.representation (GeneralLinear.reindex (finCongr _) g) v ⊗ₜ ULift.up w =
          X.1.representation g v ⊗ₜ ULift.up w
        rfl)

/-- `A × B ≅ A ⊗ ULift B`, naturally in `(A, B)`, when `B` is a representation of `GL_0`. -/
def binaryRightZeroIso (T : F.TopologicalData) (a : ℕ) :
    letI := T.topology
    T.binaryNormalizedProductFunctor.{uF, uV} a 0 ≅
      (𝟭 _).prod MixedProductTensor.liftFunctor.{uF, uV, uF} ⋙
        tensorFunctor.{uF, uF, uV, max uV uF} (GeneralLinear a F.Carrier)
          (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  NatIso.ofComponents (fun X => SmoothRep.mkIso (binaryRightZeroEquiv T a X))
    fun {X Y} f => MixedProductTensor.smoothRep_hom_ext fun v =>
      (congrArg (TensorProduct.congr (LinearEquiv.refl ℂ Y.1) ULift.moduleEquiv.symm)
        (T.binaryRightZeroTensorEquiv_naturality rfl f v)).trans
      (LinearMap.congr_fun (TensorProduct.ext' fun _ _ => rfl :
        (TensorProduct.congr (LinearEquiv.refl ℂ Y.1) ULift.moduleEquiv.symm).toLinearMap ∘ₗ
            TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap =
          TensorProduct.map (SmoothRep.hom f.1).toLinearMap
              (MixedProductTensor.liftMap (SmoothRep.hom f.2)).toLinearMap ∘ₗ
            (TensorProduct.congr (LinearEquiv.refl ℂ X.1) ULift.moduleEquiv.symm).toLinearMap)
        _)

end BinaryZero
end Langlands.AllFieldBZ.Derivative.ZeroRankTensor
