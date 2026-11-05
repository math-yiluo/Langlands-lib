import Langlands.AlgebraicGeometry.Deformation.ArtinianTests
import Langlands.GroupScheme.GeneralLinearDualNumber
import Mathlib.RingTheory.DualNumber

/-! # Actual dual-number objects in the augmented Artinian test category -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Deformation.ArtinianTest

open Langlands.GroupScheme.GeneralLinear.DualNumber

variable (k K : Type u) [CommRing k] [Field K] [Algebra k K]

/-- The residue field with its identity augmentation is an actual Artinian test. -/
def residue : ArtinianTest k K :=
  mk K (AlgHom.id k K) Function.surjective_id

private lemma dualNumber_artinian : IsArtinianRing (DualNumber K) := by
  have h : IsArtinian K (DualNumber K) :=
    inferInstanceAs (IsArtinian K (K × K))
  let : IsScalarTower K (DualNumber K) (DualNumber K) := ⟨by
    intro r x y
    apply TrivSqZeroExt.ext
    · change (r * x.fst) * y.fst = r * (x.fst * y.fst)
      exact mul_assoc _ _ _
    · change (r * x.fst) * y.snd + (r * x.snd) * y.fst =
        r * (x.fst * y.snd + x.snd * y.fst)
      ring⟩
  exact isArtinian_of_tower K (S := DualNumber K) h

/-- Dual numbers over the residue field, retaining the original base algebra. -/
def dualNumbers : ArtinianTest k K := by
  let := dualNumber_artinian K
  exact mk (DualNumber K) (TrivSqZeroExt.fstHom k K K)
    (fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩)

/-- The actual dual-number augmentation in the test category. -/
def dualReduction : dualNumbers k K ⟶ residue k K :=
  homMk (TrivSqZeroExt.fstHom k K K) (by ext; rfl)

/-- The actual constant inclusion, which is a section only for this split test. -/
def dualSection : residue k K ⟶ dualNumbers k K :=
  homMk (TrivSqZeroExt.inlAlgHom k K K) (by ext; rfl)

@[simp]
lemma dualSection_reduction : dualSection k K ≫ dualReduction k K = 𝟙 (residue k K) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply CommAlgCat.hom_ext
  ext
  rfl

/-- The dual-number augmentation is an elementary surjection. -/
lemma dualReduction_elementary : IsElementarySurjection (dualReduction k K) := by
  refine ⟨fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩, ?_⟩
  rw [← ker_augmentation (dualNumbers k K)]
  apply le_antisymm _ bot_le
  apply Ideal.mul_le.mpr
  intro x hx y hy
  have hx' : x.fst = 0 := hx
  have hy' : y.fst = 0 := hy
  change x * y = 0
  apply TrivSqZeroExt.ext
  · change x.fst * y.fst = 0
    rw [hx', zero_mul]
  · change x.fst * y.snd + x.snd * y.fst = 0
    rw [hx', hy', zero_mul, mul_zero, zero_add]

/-- Actual epsilon scaling is an augmentation-preserving Artinian arrow. -/
def dualScale (c : K) : dualNumbers k K ⟶ dualNumbers k K :=
  homMk ((epsilonScale c).restrictScalars k) (by
    ext z
    exact epsilonScale_fst c z)

@[simp]
lemma dualScale_fst (c : K) (z : DualNumber K) :
    (toAlgHom (dualScale k K c) z).fst = z.fst :=
  epsilonScale_fst c z

@[simp]
lemma dualScale_snd (c : K) (z : DualNumber K) :
    (toAlgHom (dualScale k K c) z).snd = c * z.snd :=
  epsilonScale_snd c z

end Langlands.AlgebraicGeometry.Deformation.ArtinianTest
