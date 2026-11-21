import Langlands.Automorphic.OperatorScalarLiftComparison
import Langlands.Global.RankinSelberg.CuspidalWhittakerSmoothLift
import Langlands.Global.RankinSelberg.RealPlaceWhittakerCovariance

/-! # Analytic comparison with the actual translated Whittaker integral -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic Langlands.Global.ArchimedeanGL NumberField
open Langlands.Archimedean

universe u v

attribute [local instance] regSchemeAffine regSchemeSmooth

section RightTranslation

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- Right multiplication by an infinite element leaves the finite argument
of the actual adelic point unchanged. -/
private theorem adelicPoint_mul_infinite (a k : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) :
    adelicPoint F n (archimedeanGLCoordinates F n a) b *
      (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.ofInfinite F n k) =
      adelicPoint F n (archimedeanGLCoordinates F n (a * k)) b := by
  let e := GeneralLinearGroupPoints.adelicEquiv F n
  have he (z : InfiniteAdelicGL F n) :
      e (adelicPoint F n (archimedeanGLCoordinates F n z) b) =
        AdelicGL.ofInfinite F n z * AdelicGL.ofFinite F n b :=
    (adelicHomeomorph_adelicPoint F n (archimedeanGLCoordinates F n z) b).trans
      (congrArg (fun t => AdelicGL.ofInfinite F n t * AdelicGL.ofFinite F n b)
        ((archimedeanGLCoordinates F n).symm_apply_apply z))
  apply e.injective
  rw [map_mul, e.apply_symm_apply, he a, he (a * k)]
  rw [mul_assoc, (AdelicGL.ofFinite_commute_ofInfinite F n b k).eq, ← mul_assoc, ← map_mul]

end RightTranslation

section FunctionalRightTranslation

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : ArchimedeanGL F n →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F n)
local notation "V∞" => Langlands.Archimedean.smoothVectors I π

private theorem functionalOrbitLift_rightTranslation
    (hπ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (hdense : DenseRange (Subtype.val : V∞ → E))
    (L : V∞ →ₗ[ℂ] ℂ) (hL : IsContinuousOnSmoothVectors I π L)
    (g : InfiniteAdelicGL F n) (w : V∞) :
    functionalOrbitLift F n π hπ hdense L hL
        (smoothRepresentation I π (archimedeanGLCoordinates F n g) w) =
      ArchimedeanGL.smoothRightAction F n g (functionalOrbitLift F n π hπ hdense L hL w) := by
  apply Subtype.ext
  refine funext fun a : InfiniteAdelicGL F n => ?_
  let e := archimedeanGLCoordinates F n
  let ρ := smoothRepresentation I π
  exact ((congrArg (fun x => L (ρ x w)) (e.map_mul a g)).trans
    (congrArg (fun A : Module.End ℂ V∞ => L (A w)) (ρ.map_mul (e a) (e g)))).symm

end FunctionalRightTranslation

attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup regSmoothAddCommGroup
  regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
  (hψ : IsStandardAdditiveCharacter F ψ) (b : FiniteAdelicGL F (r + 1))

/-- Actual compact translation gives right covariance of the integral lift. -/
theorem whittakerSmoothLift_compact (k : standardInfiniteCompact F (r + 1)) (w : T.Space) :
    whittakerSmoothLift T ψ hψ b (T.realization.compactRepresentation k w) =
      ArchimedeanGL.smoothRightAction F (r + 1) k.val (whittakerSmoothLift T ψ hψ b w) := by
  apply Subtype.ext
  funext a
  exact (RealPlaceWhittaker.cuspWhittaker_compact F T ψ k w
    (adelicPoint F (r + 1) (archimedeanGLCoordinates F (r + 1) a) b)).trans
    (congrArg (cuspWhittaker F T ψ w) (adelicPoint_mul_infinite F (r + 1) a k.val b))

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F (r + 1))

variable (hπ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
variable (hdense : DenseRange (Subtype.val : Langlands.Archimedean.smoothVectors
  𝓘(ℝ, ArchimedeanMatrix F (r + 1)) π → E))
variable (L : Langlands.Archimedean.smoothVectors 𝓘(ℝ, ArchimedeanMatrix F (r + 1)) π →ₗ[ℂ] ℂ)
variable (hL : IsContinuousOnSmoothVectors 𝓘(ℝ, ArchimedeanMatrix F (r + 1)) π L)
variable (j : T.Space →ₗ[ℂ] Langlands.Archimedean.smoothVectors 𝓘(ℝ, ArchimedeanMatrix F (r + 1)) π)

set_option maxHeartbeats 50000 in
/-- An extension of the original Whittaker evaluation at one fixed finite
argument recovers the actual values on all archimedean translates of fixed
original vectors. -/
theorem functionalOrbitLift_eq_whittakerSmoothLift
    (hK : ∀ (k : standardInfiniteCompact F (r + 1)) (w : T.Space),
      j (T.realization.compactRepresentation k w) =
        smoothRepresentation 𝓘(ℝ, ArchimedeanMatrix F (r + 1)) π
          (archimedeanGLCoordinates F (r + 1) k.val) (j w))
    (hgen : ∀ (X : RealLieAlgebra F (r + 1)) (w : T.Space),
      j (T.realization.envelopingAction
        (envelopingGenerator F (r + 1) (complexify F (r + 1) X)) w) =
        smoothLieDerivative I π (realLieAlgebraToMatrix F (r + 1) X) (j w))
    (J : Subgroup (FiniteAdelicGL F (r + 1)))
    (h1 : ∀ w ∈ fixedVectors T.realization.finiteRepresentation J,
      L (j w) = cuspWhittaker F T ψ w (adelicPoint F (r + 1) 1 b))
    (w : T.Space) (hw : w ∈ fixedVectors T.realization.finiteRepresentation J) :
    functionalOrbitLift F (r + 1) π hπ hdense L hL (j w) = whittakerSmoothLift T ψ hψ b w := by
  let C : T.Space →ₗ[ℂ] SmoothFunctions F (r + 1) :=
    (functionalOrbitLift F (r + 1) π hπ hdense L hL).comp j
  let W : T.Space →ₗ[ℂ] SmoothFunctions F (r + 1) := whittakerSmoothLift T ψ hψ b
  have hCK (k : standardInfiniteCompact F (r + 1)) (z : T.Space) :
      C (T.realization.compactRepresentation k z) =
        ArchimedeanGL.smoothRightAction F (r + 1) k.val (C z) :=
    (congrArg (functionalOrbitLift F (r + 1) π hπ hdense L hL) (hK k z)).trans
      (functionalOrbitLift_rightTranslation F (r + 1) π hπ hdense L hL k.val (j z))
  have hCD (a : EnvelopingAlgebra F (r + 1)) (z : T.Space) :
      C (T.realization.envelopingAction a z) = envelopingAction F (r + 1) a (C z) :=
    functionalOrbitLift_envelopingAction F (r + 1) π hπ hdense L hL
      T.realization.envelopingAction j hgen a z
  have hC1 (z : T.Space) : (C z).val 1 = L (j z) := by
    let ρ := smoothRepresentation I π
    exact (congrArg (fun g => L (ρ g (j z))) (map_one (archimedeanGLCoordinates F (r + 1)))).trans
      (congrArg (fun A : Module.End ℂ (Langlands.Archimedean.smoothVectors I π) => L (A (j z)))
        ρ.map_one)
  have hW1 (z : T.Space) : (W z).val 1 = cuspWhittaker F T ψ z (adelicPoint F (r + 1) 1 b) :=
    congrArg (fun g => cuspWhittaker F T ψ z (adelicPoint F (r + 1) g b))
      (map_one (archimedeanGLCoordinates F (r + 1)))
  have hAt1 (z : T.Space) (hz : z ∈ fixedVectors T.realization.finiteRepresentation J) :
      (C z).val 1 = (W z).val 1 :=
    (hC1 z).trans ((h1 z hz).trans (hW1 z).symm)
  exact OperatorRealization.scalarLifts_eq_of_agree_at_fixedLevel T.realization J C W
    hCK (whittakerSmoothLift_compact T ψ hψ b) hCD (whittakerSmoothLift_envelopingAction T ψ hψ b)
    hAt1 w hw

/-- Exact fixed-level comparison of the genuine smooth orbit evaluation
with the original cuspidal Whittaker integral. -/
def CuspidalWhittakerOrbitComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (b : FiniteAdelicGL F (r + 1))
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E)),
    let model := 𝓘(ℝ, ArchimedeanMatrix F (r + 1))
    let V := Langlands.Archimedean.smoothVectors model π
    ∀ (hπ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
      (hdense : DenseRange (Subtype.val : V → E))
      (L : V →ₗ[ℂ] ℂ) (hL : IsContinuousOnSmoothVectors model π L)
      (j : T.Space →ₗ[ℂ] V),
      (∀ (k : standardInfiniteCompact F (r + 1)) (w : T.Space),
        j (T.realization.compactRepresentation k w) =
          smoothRepresentation model π (archimedeanGLCoordinates F (r + 1) k.val) (j w)) →
      (∀ (X : RealLieAlgebra F (r + 1)) (w : T.Space),
        j (T.realization.envelopingAction
          (envelopingGenerator F (r + 1) (complexify F (r + 1) X)) w) =
          smoothLieDerivative model π (realLieAlgebraToMatrix F (r + 1) X) (j w)) →
      ∀ (J : Subgroup (FiniteAdelicGL F (r + 1))),
        (∀ w ∈ fixedVectors T.realization.finiteRepresentation J,
          L (j w) = cuspWhittaker F T ψ w (adelicPoint F (r + 1) 1 b)) →
        ∀ w ∈ fixedVectors T.realization.finiteRepresentation J,
          functionalOrbitLift F (r + 1) π hπ hdense L hL (j w) =
            whittakerSmoothLift T ψ hψ b w

theorem cuspidalWhittakerOrbitComparison : CuspidalWhittakerOrbitComparisonStatement.{u,v} := by
  intro F _ _ _ r T ψ hψ b E _ _ _ π
  dsimp only
  intro hπ hdense L hL j hK hgen J h1 w hw
  exact functionalOrbitLift_eq_whittakerSmoothLift T ψ hψ b π hπ hdense L hL j
    hK hgen J h1 w hw

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
