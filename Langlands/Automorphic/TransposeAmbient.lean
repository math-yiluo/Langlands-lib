import Langlands.Automorphic.Smooth
import Langlands.Global.AdelicGLInverseTranspose

/-! # Inverse-transpose pullback on the rational continuous ambient space -/

noncomputable section
universe u

namespace Langlands.Global.AdelicGL

open NumberField IsDedekindDomain Langlands.GeneralLinear

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

@[simp]
theorem inverseTranspose_pair (a : InfiniteAdelicGL K n) (b : FiniteAdelicGL K n) :
    inverseTranspose n (AdeleRing (𝓞 K) K) (pair K n a b) =
      pair K n (inverseTranspose n (InfiniteAdeleRing K) a)
        (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) b) := by
  apply (split K n).injective
  change (infinite K n _, finite K n _) = (infinite K n _, finite K n _)
  simp only [RankinSelbergGlobal.Unfolding.infinite_inverseTranspose,
    RankinSelbergGlobal.Unfolding.finite_inverseTranspose,
    infinite_pair, finite_pair]

end Langlands.Global.AdelicGL

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear NumberField IsDedekindDomain
open ContinuousRationalFunctions

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance transposeAmbientRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance transposeAmbientContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _

/-- Pullback by inverse transpose preserves actual rational invariance and continuity. -/
def continuousTranspose :
    ContinuousRationalFunctions K n ≃ₗ[ℂ] ContinuousRationalFunctions K n :=
  let t : ContinuousRationalFunctions K n →ₗ[ℂ] ContinuousRationalFunctions K n :=
    { toFun f :=
        ⟨⟨fun g => evaluate K n f (inverseTranspose n (AdeleRing (𝓞 K) K) g), by
          intro γ g
          change evaluate K n f (inverseTranspose n (AdeleRing (𝓞 K) K)
            (AdelicGL.rational K n γ * g)) = _
          rw [map_mul, Langlands.Automorphic.inverseTranspose_rational]
          exact evaluate_rational K n f _ _⟩,
          (continuous_evaluate K n f).comp (continuous_inverseTranspose n _)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  { toLinearMap := t
    invFun := t
    left_inv f := by
      apply Subtype.ext
      apply Subtype.ext
      funext g
      exact congrArg (evaluate K n f) (inverseTranspose_involutive n _ g)
    right_inv f := by
      apply Subtype.ext
      apply Subtype.ext
      funext g
      exact congrArg (evaluate K n f) (inverseTranspose_involutive n _ g) }

@[simp]
theorem evaluate_continuousTranspose (f : ContinuousRationalFunctions K n)
    (g : AdelicGL K n) :
    evaluate K n (continuousTranspose K n f) g =
      evaluate K n f (inverseTranspose n (AdeleRing (𝓞 K) K) g) := rfl

@[simp]
theorem continuousTranspose_involutive (f : ContinuousRationalFunctions K n) :
    continuousTranspose K n (continuousTranspose K n f) = f :=
  (continuousTranspose K n).left_inv f

@[simp]
theorem continuousTranspose_symm :
    (continuousTranspose K n).symm = continuousTranspose K n := rfl

/-- The pullback exchanges right translation with its inverse-transpose twist. -/
theorem continuousTranspose_rightAction (g : AdelicGL K n)
    (f : ContinuousRationalFunctions K n) :
    continuousTranspose K n (continuousRightAction K n g f) =
      continuousRightAction K n (inverseTranspose n (AdeleRing (𝓞 K) K) g)
        (continuousTranspose K n f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evaluate K n f (inverseTranspose n (AdeleRing (𝓞 K) K) x * g) =
    evaluate K n f (inverseTranspose n (AdeleRing (𝓞 K) K)
      (x * inverseTranspose n (AdeleRing (𝓞 K) K) g))
  rw [map_mul, inverseTranspose_involutive]

/-- Both the finite slice and the infinite argument are reindexed by inverse transpose. -/
theorem infiniteSlice_continuousTranspose (b : FiniteAdelicGL K n)
    (f : ContinuousRationalFunctions K n) :
    infiniteSlice K n b (continuousTranspose K n f) =
      fun a => infiniteSlice K n
        (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) b) f
        (inverseTranspose n (InfiniteAdeleRing K) a) := by
  funext a
  change evaluate K n f (inverseTranspose n (AdeleRing (𝓞 K) K)
    (AdelicGL.pair K n a b)) = _
  rw [AdelicGL.inverseTranspose_pair]
  rfl

/-- An open finite stabilizer pulls back to an open finite stabilizer. -/
theorem continuousTranspose_mem_finiteSmooth {f : ContinuousRationalFunctions K n}
    (hf : f ∈ finiteSmoothSubrepresentation K n) :
    continuousTranspose K n f ∈ finiteSmoothSubrepresentation K n := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨L.comap (inverseTranspose n (FiniteAdeleRing (𝓞 K) K)).toMonoidHom
    (continuous_inverseTranspose n _), ?_⟩
  intro l
  have hl := hL ⟨inverseTranspose n (FiniteAdeleRing (𝓞 K) K) l.val, l.property⟩
  change continuousRightAction K n
    (AdelicGL.ofFinite K n (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) l.val)) f = f at hl
  change continuousRightAction K n (AdelicGL.ofFinite K n l.val)
    (continuousTranspose K n f) = continuousTranspose K n f
  simpa only [continuousTranspose_rightAction, Langlands.Global.RankinSelbergGlobal.Unfolding.inverseTranspose_ofFinite,
    inverseTranspose_involutive] using congrArg (continuousTranspose K n) hl

@[simp]
theorem continuousTranspose_mem_finiteSmooth_iff (f : ContinuousRationalFunctions K n) :
    continuousTranspose K n f ∈ finiteSmoothSubrepresentation K n ↔
      f ∈ finiteSmoothSubrepresentation K n := by
  constructor
  · intro hf
    simpa only [continuousTranspose_involutive] using
      continuousTranspose_mem_finiteSmooth K n hf
  · exact continuousTranspose_mem_finiteSmooth K n

/-- Pullback preserves existence of an actual compact open finite level. -/
theorem hasFiniteLevel_continuousTranspose {f : ContinuousRationalFunctions K n}
    (hf : HasFiniteLevel K n f) : HasFiniteLevel K n (continuousTranspose K n f) := by
  obtain ⟨L, ho, hc, hL⟩ := hf
  let t := inverseTransposeContinuous n (FiniteAdeleRing (𝓞 K) K)
  refine ⟨L.comap t.toMonoidHom, ho.preimage t.continuous, ?_, ?_⟩
  · exact t.toHomeomorph.isCompact_preimage.mpr hc
  · intro l
    have h := congrArg (continuousTranspose K n) (hL ⟨t l.val, l.property⟩)
    simpa only [t, inverseTransposeContinuous_apply, continuousTranspose_rightAction,
      Langlands.Global.RankinSelbergGlobal.Unfolding.inverseTranspose_ofFinite, inverseTranspose_involutive] using h

@[simp]
theorem hasFiniteLevel_continuousTranspose_iff (f : ContinuousRationalFunctions K n) :
    HasFiniteLevel K n (continuousTranspose K n f) ↔ HasFiniteLevel K n f := by
  constructor
  · intro hf
    simpa only [continuousTranspose_involutive] using
      hasFiniteLevel_continuousTranspose K n hf
  · exact hasFiniteLevel_continuousTranspose K n

end Langlands.Automorphic
