import Langlands.Global.RankinSelberg.CuspidalWhittakerOrbitComparison

/-! # Actual translated values of a fixed-level smooth Whittaker evaluation -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic Langlands.Global.ArchimedeanGL NumberField Langlands.Archimedean

universe u v

attribute [local instance] regSchemeAffine regSchemeSmooth regRationalAddCommGroup
  regContinuousAddCommGroup regSmoothAddCommGroup regFormsAddCommGroup regStableAddCommGroup
  regRealizationAddCommGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
  (hψ : IsStandardAdditiveCharacter F ψ) (d : FiniteAdelicGL F (r + 1))

include hψ

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F (r + 1))

section InfiniteValues

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))

/-- The analytic comparison evaluated at the specified archimedean
matrix gives the actual translated Whittaker integral. -/
theorem fixedLevel_functional_infinite_value
    (hπ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (hdense : DenseRange (Subtype.val : Langlands.Archimedean.smoothVectors I π → E))
    (L : Langlands.Archimedean.smoothVectors I π →ₗ[ℂ] ℂ)
    (hL : IsContinuousOnSmoothVectors I π L)
    (j : T.Space →ₗ[ℂ] Langlands.Archimedean.smoothVectors I π)
    (hK : ∀ (k : standardInfiniteCompact F (r + 1)) (w : T.Space),
      j (T.realization.compactRepresentation k w) =
        smoothRepresentation I π (archimedeanGLCoordinates F (r + 1) k.val) (j w))
    (hgen : ∀ (X : RealLieAlgebra F (r + 1)) (w : T.Space),
      j (T.realization.envelopingAction
        (envelopingGenerator F (r + 1) (complexify F (r + 1) X)) w) =
        smoothLieDerivative I π (realLieAlgebraToMatrix F (r + 1) X) (j w))
    (J : Subgroup (FiniteAdelicGL F (r + 1)))
    (h1 : ∀ w ∈ Langlands.fixedVectors T.realization.finiteRepresentation J,
      L (j w) = cuspWhittaker F T ψ w (adelicPoint F (r + 1) 1 d))
    (w : T.Space) (hw : w ∈ Langlands.fixedVectors T.realization.finiteRepresentation J)
    (a : ArchimedeanGL F (r + 1)) :
    L (smoothRepresentation I π a (j w)) =
      cuspWhittaker F T ψ w (adelicPoint F (r + 1) a d) := by
  let e := archimedeanGLCoordinates F (r + 1)
  have h := congrArg (fun f : SmoothFunctions F (r + 1) => f.val (e.symm a))
    (functionalOrbitLift_eq_whittakerSmoothLift T ψ hψ d π hπ hdense L hL j hK hgen J h1 w hw)
  simpa only [functionalOrbitLift_apply, whittakerSmoothLift_apply, e,
    ContinuousMulEquiv.apply_symm_apply] using h

end InfiniteValues

section InfiniteCovariance

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))

local notation "V" => Langlands.Archimedean.smoothVectors I π

/-- The original fixed-level image satisfies the generic Whittaker
character law under each infinite adelic unipotent translation. -/
theorem fixedLevel_functional_infinite_character
    (hπ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (hdense : DenseRange (Subtype.val : V → E))
    (L : V →ₗ[ℂ] ℂ) (hL : IsContinuousOnSmoothVectors I π L)
    (j : T.Space →ₗ[ℂ] V)
    (hK : ∀ (k : standardInfiniteCompact F (r + 1)) (w : T.Space),
      j (T.realization.compactRepresentation k w) =
        smoothRepresentation I π (archimedeanGLCoordinates F (r + 1) k.val) (j w))
    (hgen : ∀ (X : RealLieAlgebra F (r + 1)) (w : T.Space),
      j (T.realization.envelopingAction
        (envelopingGenerator F (r + 1) (complexify F (r + 1) X)) w) =
        smoothLieDerivative I π (realLieAlgebraToMatrix F (r + 1) X) (j w))
    (J : Subgroup (FiniteAdelicGL F (r + 1)))
    (h1 : ∀ w ∈ Langlands.fixedVectors T.realization.finiteRepresentation J,
      L (j w) = cuspWhittaker F T ψ w (adelicPoint F (r + 1) 1 d))
    (z : unipotentAdelic F (r + 1)) (hz : finPart F (r + 1) z.val = 1)
    (w : T.Space) (hw : w ∈ Langlands.fixedVectors T.realization.finiteRepresentation J) :
    L (smoothRepresentation I π (archPart F (r + 1) z.val) (j w)) =
      (genericCharacter F r ψ (fun _ => 1) z : ℂ) * L (j w) := by
  let a := archPart F (r + 1) z.val
  have hmul : z.val * adelicPoint F (r + 1) 1 d =
      adelicPoint F (r + 1) a d :=
    (mul_adelicPoint F (r + 1) z.val 1 d).trans
      (congrArg₂ (adelicPoint F (r + 1)) (mul_one a)
        ((congrArg (fun f : FiniteAdelicGL F (r + 1) => f * d) hz).trans (one_mul d)))
  calc
    _ = cuspWhittaker F T ψ w (adelicPoint F (r + 1) a d) :=
      fixedLevel_functional_infinite_value T ψ hψ d π hπ hdense L hL j hK hgen J h1 w hw a
    _ = cuspWhittaker F T ψ w (z.val * adelicPoint F (r + 1) 1 d) :=
      congrArg (cuspWhittaker F T ψ w) hmul.symm
    _ = genericCharacter F r ψ (fun _ => 1) z *
        cuspWhittaker F T ψ w (adelicPoint F (r + 1) 1 d) :=
      Unfolding.cuspWhittaker_mul_left F T ψ hψ w z (adelicPoint F (r + 1) 1 d)
    _ = _ := congrArg (fun s : ℂ => genericCharacter F r ψ (fun _ => 1) z * s) (h1 w hw).symm

end InfiniteCovariance

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
