import Langlands.Global.AdelicGLTopology
import Langlands.Global.RankinSelberg.CuspidalFixedWhittakerValues
import Langlands.Representation.Archimedean.MixedSmoothExtension

/-! # Actual Whittaker evaluations on the mixed smooth space -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic Langlands.Global.ArchimedeanGL NumberField Langlands.Archimedean
  Langlands.Archimedean.MixedSmooth Langlands.Archimedean.SmoothInvariantSubspace

universe u v

attribute [local instance] regSchemeAffine regSchemeSmooth regRationalAddCommGroup
  regContinuousAddCommGroup regSmoothAddCommGroup regFormsAddCommGroup regStableAddCommGroup
  regRealizationAddCommGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
  (hψ : IsStandardAdditiveCharacter F ψ)

/-- The actual integral at infinite identity as a linear map on the original
carrier, indexed by its finite adelic argument. -/
def finiteWhittakerEvaluation (d : FiniteAdelicGL F (r + 1)) : T.Space →ₗ[ℂ] ℂ :=
  UnramifiedWhittaker.whittakerFunctional F ψ hψ T (adelicPoint F (r + 1) 1 d)

@[simp]
theorem finiteWhittakerEvaluation_apply (d : FiniteAdelicGL F (r + 1)) (w : T.Space) :
    finiteWhittakerEvaluation T ψ hψ d w = cuspWhittaker F T ψ w (adelicPoint F (r + 1) 1 d) :=
  rfl

/-- Right finite translation of the actual evaluation multiplies its
finite adelic argument on the right. -/
theorem finiteWhittakerEvaluation_translate (d a : FiniteAdelicGL F (r + 1)) (w : T.Space) :
    finiteWhittakerEvaluation T ψ hψ d (T.realization.finiteRepresentation a w) =
      finiteWhittakerEvaluation T ψ hψ (d * a) w := by
  have he : adelicPoint F (r + 1) 1 a =
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm (AdelicGL.ofFinite F (r + 1) a) := by
    apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
    rw [MulEquiv.apply_symm_apply]
    have hc := adelicHomeomorph_adelicPoint F (r + 1) 1 a
    change GeneralLinearGroupPoints.adelicEquiv F (r + 1) (adelicPoint F (r + 1) 1 a) =
      AdelicGL.ofInfinite F (r + 1) ((archimedeanGLCoordinates F (r + 1)).symm 1) *
        AdelicGL.ofFinite F (r + 1) a at hc
    simpa only [map_one, one_mul] using hc
  have ha : adelicPoint F (r + 1) 1 d * adelicPoint F (r + 1) 1 a =
      adelicPoint F (r + 1) 1 (d * a) :=
    (adelicPoint_mul F (r + 1) 1 1 d a).symm.trans
      (congrArg (fun x => adelicPoint F (r + 1) x (d * a)) (one_mul 1))
  simp only [finiteWhittakerEvaluation_apply,
    UnramifiedWhittaker.cuspWhittaker_finiteRepresentation, ← he, ha]

section Mixed

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NonarchimedeanGroup (FiniteAdelicGL F (r + 1))]
  (σ : FiniteAdelicGL F (r + 1) →* (E →L[ℂ] E))
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))
  (hcomm : ∀ g d x, π g (σ d x) = σ d (π g x))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F (r + 1))
local notation "S" => Langlands.Archimedean.smoothVectors I π
local notation "ρ" => T.realization.finiteRepresentation
local notation "W" => Vectors (A := ArchimedeanMatrix F (r + 1)) σ π hcomm
local notation "B" => finiteWhittakerEvaluation T ψ hψ

variable (j : T.Space →ₗ[ℂ] Langlands.Archimedean.smoothVectors 𝓘(ℝ, ArchimedeanMatrix F (r + 1)) π)

variable
  (exts : EvaluationExtensions (A := ArchimedeanMatrix F (r + 1)) (G := ArchimedeanGL F (r + 1))
    T.realization.finiteRepresentation π j (finiteWhittakerEvaluation T ψ hψ))
  (hd : DenseFixedImages (A := ArchimedeanMatrix F (r + 1)) (G := ArchimedeanGL F (r + 1))
    T.realization.finiteRepresentation σ π j)

/-- The linear mixed-smooth evaluation whose restriction to each compact
open level is the given extension of the original integral there. -/
def mixedWhittakerEvaluation (d : FiniteAdelicGL F (r + 1)) : W →ₗ[ℂ] ℂ :=
  extendedEvaluation (A := ArchimedeanMatrix F (r + 1)) (G := ArchimedeanGL F (r + 1))
    (L := FiniteAdelicGL F (r + 1)) (V₀ := T.Space) ρ σ π hcomm j B exts hd d

/-- Finite covariance of the glued actual evaluations. -/
theorem mixedWhittakerEvaluation_finite
    (hj : ∀ a v, finiteOnSmooth (A := ArchimedeanMatrix F (r + 1)) σ π hcomm a (j v) = j (ρ a v))
    (d a : FiniteAdelicGL F (r + 1)) (w : W) :
    mixedWhittakerEvaluation T ψ hψ σ π hcomm j exts hd d
      (MixedSmooth.finiteRepresentation σ π hcomm a w) =
    mixedWhittakerEvaluation T ψ hψ σ π hcomm j exts hd (d * a) w :=
  extendedEvaluation_finite (A := ArchimedeanMatrix F (r + 1)) (G := ArchimedeanGL F (r + 1))
    (L := FiniteAdelicGL F (r + 1)) (V₀ := T.Space) ρ σ π hcomm j B exts hd hj
    (finiteWhittakerEvaluation_translate T ψ hψ) d a w

variable [CompleteSpace E]

/-- Evaluation at identity on a mixed-smooth translate of an original vector
recovers the actual cusp Whittaker function. -/
theorem mixedWhittakerEvaluation_translated_value
    (hj : ∀ a v, finiteOnSmooth (A := ArchimedeanMatrix F (r + 1)) σ π hcomm a (j v) = j (ρ a v))
    (hπ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (hdense : DenseRange (Subtype.val : S → E))
    (hK : ∀ (k : standardInfiniteCompact F (r + 1)) (w : T.Space),
      j (T.realization.compactRepresentation k w) =
        smoothRepresentation I π (archimedeanGLCoordinates F (r + 1) k.val) (j w))
    (hgen : ∀ (X : RealLieAlgebra F (r + 1)) (w : T.Space),
      j (T.realization.envelopingAction
        (envelopingGenerator F (r + 1) (complexify F (r + 1) X)) w) =
        smoothLieDerivative I π (realLieAlgebraToMatrix F (r + 1) X) (j w))
    (v₀ : T.Space) (a : ArchimedeanGL F (r + 1)) (d : FiniteAdelicGL F (r + 1)) :
    mixedWhittakerEvaluation T ψ hψ σ π hcomm j exts hd 1
      (MixedSmooth.finiteRepresentation σ π hcomm d
        (MixedSmooth.archimedeanRepresentation σ π hcomm a
          (sourceToMixed ρ σ π hcomm j T.realization.finiteRepresentation_isSmooth hj v₀))) =
    cuspWhittaker F T ψ v₀ (adelicPoint F (r + 1) a d) :=
  extendedEvaluation_translate_source (A := ArchimedeanMatrix F (r + 1))
    (G := ArchimedeanGL F (r + 1)) (V₀ := T.Space)
    ρ σ π hcomm j B exts hd T.realization.finiteRepresentation_isSmooth hj
    (finiteWhittakerEvaluation_translate T ψ hψ)
    (fun a d v => cuspWhittaker F T ψ v (adelicPoint F (r + 1) a d))
    (fun a d J v hv => fixedLevel_functional_infinite_value T ψ hψ d π hπ hdense
      (exts.level d J) (exts.continuous_level d J) j hK hgen J.toSubgroup (exts.agrees d J) v hv a)
    a d v₀

/-- The identity functional on the mixed smooth space has the actual
adelic Whittaker character under every upper unipotent translation. -/
theorem mixedWhittakerEvaluation_unipotent
    (hj : ∀ a v, finiteOnSmooth (A := ArchimedeanMatrix F (r + 1)) σ π hcomm a (j v) = j (ρ a v))
    (hπ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (hdense : DenseRange (Subtype.val : S → E))
    (hK : ∀ (k : standardInfiniteCompact F (r + 1)) (w : T.Space),
      j (T.realization.compactRepresentation k w) =
        smoothRepresentation I π (archimedeanGLCoordinates F (r + 1) k.val) (j w))
    (hgen : ∀ (X : RealLieAlgebra F (r + 1)) (w : T.Space),
      j (T.realization.envelopingAction
        (envelopingGenerator F (r + 1) (complexify F (r + 1) X)) w) =
        smoothLieDerivative I π (realLieAlgebraToMatrix F (r + 1) X) (j w))
    (z : unipotentAdelic F (r + 1)) (w : W) :
    mixedWhittakerEvaluation T ψ hψ σ π hcomm j exts hd 1
      (MixedSmooth.finiteRepresentation σ π hcomm (finPart F (r + 1) z.val)
        (MixedSmooth.archimedeanRepresentation σ π hcomm (archPart F (r + 1) z.val) w)) =
    (genericCharacter F r ψ (fun _ => 1) z : ℂ) *
      mixedWhittakerEvaluation T ψ hψ σ π hcomm j exts hd 1 w := by
  let a := archPart F (r + 1) z.val
  let d := finPart F (r + 1) z.val
  let c : ℂ := genericCharacter F r ψ (fun _ => 1) z
  have hp : z.val * adelicPoint F (r + 1) 1 1 = adelicPoint F (r + 1) a d :=
    (mul_adelicPoint F (r + 1) z.val 1 1).trans
      (congrArg₂ (adelicPoint F (r + 1)) (mul_one a) (mul_one d))
  refine extendedEvaluation_covariance_of_fixedImages
    (A := ArchimedeanMatrix F (r + 1)) (G := ArchimedeanGL F (r + 1)) (V₀ := T.Space)
    ρ σ π hcomm j B exts hd hj (finiteWhittakerEvaluation_translate T ψ hψ)
    a d c ?_ w
  intro J v
  calc
    _ = cuspWhittaker F T ψ v.val (adelicPoint F (r + 1) a d) :=
      fixedLevel_functional_infinite_value T ψ hψ d π hπ hdense (exts.level d J)
        (exts.continuous_level d J) j hK hgen J.toSubgroup (exts.agrees d J) v.val v.property a
    _ = cuspWhittaker F T ψ v.val (z.val * adelicPoint F (r + 1) 1 1) :=
      congrArg (cuspWhittaker F T ψ v.val) hp.symm
    _ = c * finiteWhittakerEvaluation T ψ hψ 1 v.val :=
      Unfolding.cuspWhittaker_mul_left F T ψ hψ v.val z (adelicPoint F (r + 1) 1 1)
    _ = _ := congrArg (fun x : ℂ => c * x) (exts.agrees 1 J v.val v.property).symm

end Mixed

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
