import Langlands.Representation.Archimedean.RealTemperedTwistReduction
import Langlands.Representation.Archimedean.RealTemperedCommutantReduction

/-!
# Transporting tempered form and commutant data through determinant twists

The two analytical inputs of `RealTemperedCommutantReduction` pull back along
the determinant twist. Infinitesimal scalar slack is preserved by pullback,
and conjugation of an endomorphism preserves the simultaneous commutant.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

namespace RealTemperedTwist

open InductionStages RealTemperedCommutantReduction

variable {n : ℕ}

/-- Pullback of a linear-first sesquilinear form along the determinant twist. -/
def pullbackForm (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n)
    (B : KFin n (ds.map (realBlockTwist s)) →ₗ[ℂ]
      KFin n (ds.map (realBlockTwist s)) →ₗ⋆[ℂ] ℂ) :
    KFin n ds →ₗ[ℂ] KFin n ds →ₗ⋆[ℂ] ℂ where
  toFun v :=
    { toFun := fun w => B (twistEquiv s ds hr v) (twistEquiv s ds hr w)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  map_add' := by intros; ext w; simp
  map_smul' := by intros; ext w; simp

theorem pullbackForm_apply (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n)
    (B : KFin n (ds.map (realBlockTwist s)) →ₗ[ℂ]
      KFin n (ds.map (realBlockTwist s)) →ₗ⋆[ℂ] ℂ) (v w : KFin n ds) :
    pullbackForm s ds hr B v w = B (twistEquiv s ds hr v) (twistEquiv s ds hr w) :=
  rfl

/-- Sufficient form data pull back through any real determinant twist. -/
theorem hasTemperedForm_of_twist (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n)
    (hform : HasTemperedForm n (ds.map (realBlockTwist s))) :
    HasTemperedForm n ds := by
  obtain ⟨hne, B, hB, hBK, hBL⟩ := hform
  let := hne
  refine ⟨(twistEquiv s ds hr).toEquiv.nontrivial, pullbackForm s ds hr B, ?_, ?_, ?_⟩
  · intro v hv
    apply (twistEquiv s ds hr).injective
    simpa only [map_zero] using hB (twistEquiv s ds hr v) hv
  · intro k v w
    change B (twistEquiv s ds hr (realStandardRep n ds k v))
      (twistEquiv s ds hr (realStandardRep n ds k w)) =
        B (twistEquiv s ds hr v) (twistEquiv s ds hr w)
    rw [twistEquiv_rep, twistEquiv_rep]
    exact hBK k _ _
  · intro X
    obtain ⟨c, hc⟩ := hBL X
    obtain ⟨d, hd⟩ := twistEquiv_lie_shift s ds hr (1 ⊗ₜ X)
    refine ⟨c - d - (starRingEnd ℂ) d, fun v w => ?_⟩
    have h := hc (twistEquiv s ds hr v) (twistEquiv s ds hr w)
    rw [hd, hd] at h
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      map_smulₛₗ, smul_eq_mul] at h
    change B (twistEquiv s ds hr (realStandardLie n ds (1 ⊗ₜ X) v))
        (twistEquiv s ds hr w) +
      B (twistEquiv s ds hr v)
        (twistEquiv s ds hr (realStandardLie n ds (1 ⊗ₜ X) w)) =
      (c - d - (starRingEnd ℂ) d) *
        B (twistEquiv s ds hr v) (twistEquiv s ds hr w)
    linear_combination h

/-- Scalar simultaneous commutants pull back through real determinant twists. -/
theorem hasScalarCommutant_of_twist (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n)
    (hcomm : HasScalarCommutant n (ds.map (realBlockTwist s))) :
    HasScalarCommutant n ds := by
  intro E hEK hEL
  let e := twistEquiv s ds hr
  let T : KFin n (ds.map (realBlockTwist s)) →ₗ[ℂ]
      KFin n (ds.map (realBlockTwist s)) :=
    e.toLinearMap ∘ₗ E ∘ₗ e.symm.toLinearMap
  have hT (v : KFin n ds) : T (e v) = e (E v) := by simp [T]
  have heK (k : Matrix.unitaryGroup (Fin n) ℝ) (v : KFin n ds) :
      e (realStandardRep n ds k v) =
        realStandardRep n (ds.map (realBlockTwist s)) k (e v) :=
    twistEquiv_rep s ds hr k v
  have hTK (k : Matrix.unitaryGroup (Fin n) ℝ)
      (v : KFin n (ds.map (realBlockTwist s))) :
      T (realStandardRep n (ds.map (realBlockTwist s)) k v) =
        realStandardRep n (ds.map (realBlockTwist s)) k (T v) := by
    obtain ⟨f, rfl⟩ := e.surjective v
    rw [← heK, hT, hT, hEK, heK]
  have hTL (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)
      (v : KFin n (ds.map (realBlockTwist s))) :
      T (realStandardLie n (ds.map (realBlockTwist s)) Z v) =
        realStandardLie n (ds.map (realBlockTwist s)) Z (T v) := by
    obtain ⟨f, rfl⟩ := e.surjective v
    obtain ⟨d, hd⟩ := twistEquiv_lie_shift s ds hr Z
    change ∀ f, realStandardLie n (ds.map (realBlockTwist s)) Z (e f) =
      e (realStandardLie n ds Z f) + d • e f at hd
    rw [hd, map_add, map_smul, hT, hT, hEL, ← hd]
  obtain ⟨c, hc⟩ := hcomm T hTK hTL
  refine ⟨c, fun v => ?_⟩
  apply e.injective
  calc
    e (E v) = T (e v) := (hT v).symm
    _ = c • e v := hc _
    _ = e (c • v) := (e.map_smul c v).symm

end RealTemperedTwist

end Langlands.Archimedean
