import Langlands.GroupScheme.SplitUnipotentTorsor.VectorRetract
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof

/-! # Vector-quotient series over an arbitrary affine base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot SplitUnipotentAffineTorsor

/-- A finite series whose successive represented fppf quotients are finite-dimensional
vector groups. No connectedness of the base or the total spaces is required. -/
def HasAffineVectorSeries {R : CommRingCat.{u}} :
    ℕ → GroupScheme (Spec R) → Prop
  | 0, H => SubgroupFunctor.range (𝟙 H) = ⊥
  | n + 1, H =>
      ∃ (K V : GroupScheme (Spec R)) (j : K ⟶ H) (q : H ⟶ V),
        IsClosedSubgroup j ∧ IsFppfQuotient (SubgroupFunctor.range j) q ∧
          IsVectorGroup V ∧ HasAffineVectorSeries n K

namespace HasAffineVectorSeries

variable {R : CommRingCat.{u}}

/-- An existing split-unipotent series gives a vector-quotient series. -/
theorem of_hasSplitSeries {n : ℕ} {H : GroupScheme (Spec R)}
    (h : HasSplitSeries n H) : HasAffineVectorSeries n H := by
  induction n generalizing H with
  | zero => exact h
  | succ n ih =>
      obtain ⟨K, V, j, q, hj, _, _, _, hq, hV, hK⟩ := h
      exact ⟨K, V, j, q, hj, hq, ⟨1, hV⟩, ih hK⟩

/-- Cocycles of an affine group with a finite vector-quotient series vanish on every
base change to an affine scheme, over an arbitrary commutative ring. -/
theorem cocyclesVanish :
    ∀ (n : ℕ) (H : GroupScheme (Spec R)), HasAffineVectorSeries n H →
      IsAffineHom H.X.hom → CocyclesVanish H
  | 0, _, h, _ => cocyclesVanish_of_range_id_eq_bot h
  | n + 1, H, ⟨K, V, j, q, hj, ⟨_, _, _, hjq⟩, ⟨d, hV⟩, hK⟩, _ => by
      have : IsClosedImmersion j.hom.hom.left := hj
      have : Mono j.hom.hom := Over.mono_of_mono_left _
      have : IsAffineHom K.X.hom := by
        rw [← Over.w j.hom.hom]
        infer_instance
      have hKv := cocyclesVanish n K hK this
      have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
      have : IsAffineHom V.X.hom := hV.isAffineHom_overRing
      have : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
      obtain ⟨σ, hσ⟩ := exists_section j q hjq hKv
      exact cocyclesVanish_of_section j q hjq σ hσ
        (fun T _ U _ _ _ ξ => ξ.isTrivial_of_isVectorGroupOfDimension hV T U) hKv

end HasAffineVectorSeries

end Langlands.GroupScheme
