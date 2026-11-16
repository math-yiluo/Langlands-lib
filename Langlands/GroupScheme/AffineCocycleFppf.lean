import Langlands.GroupScheme.CocycleAffineRefinement
import Langlands.GroupScheme.CocycleRestriction
import Langlands.GroupScheme.AffineVectorSeries
import Langlands.GroupScheme.SplitUnipotentTorsor.ProjectiveVector

/-! # Affine cocycle vanishing on arbitrary single fppf covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitUnipotentAffineTorsor

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)}

/-- Affine cocycle vanishing also applies directly to the original group,
without retaining an identity base change in the conclusion. -/
theorem CocyclesVanish.isTrivial_on_affine (hH : CocyclesVanish H)
    (U : Over (Spec R)) [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (ξ : Cocycle H U) : ξ.IsTrivial := by
  let b := 𝟙 (Spec R)
  let V := (Over.map b).obj U
  let : IsAffine (Over.mk b).left := by
    change IsAffine (Spec R)
    infer_instance
  let : IsAffine V.left := by
    change IsAffine U.left
    infer_instance
  let : Flat V.hom := by
    simpa [V, b] using (inferInstance : Flat U.hom)
  let : Surjective V.hom := by
    simpa [V, b] using (inferInstance : Surjective U.hom)
  let r : V ⟶ U := Over.homMk (𝟙 U.left) (by simp [V, b])
  let ζ := ξ.refine r
  have hζ : ζ.IsTrivial := Cocycle.IsTrivial.of_baseChangeAlong b
    (hH (Over.mk b) U (ζ.baseChangeAlong b U (𝟙 _)))
  exact hζ.of_refine_fpqcCover r

/-- Affine cocycle vanishing gives original-cover triviality on every single
fppf cover of the ring spectrum. -/
theorem CocyclesVanish.isTrivial_on_fppf (hH : CocyclesVanish H)
    (U : Over (Spec R)) [Flat U.hom] [Surjective U.hom]
    [LocallyOfFinitePresentation U.hom] (ξ : Cocycle H U) : ξ.IsTrivial := by
  apply ξ.isTrivial_of_affine_fppf
  intro W _ _ _ _ ζ
  exact hH.isTrivial_on_affine W ζ

/-- The same extension applies after every affine base change. -/
theorem CocyclesVanish.isTrivial_on_fppf_baseChange (hH : CocyclesVanish H)
    (T : Over (Spec R)) [IsAffine T.left] (U : Over T.left)
    [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom]
    (ξ : Cocycle ((GroupScheme.baseChange T.hom).obj H) U) : ξ.IsTrivial := by
  apply ξ.isTrivial_of_affine_fppf
  intro W _ _ _ _ ζ
  exact hH T W ζ

end SplitUnipotentAffineTorsor

namespace Cocycle

variable {B : Scheme.{u}} {V : GroupScheme B}

/-- Finite-dimensional vector-group cocycles vanish on arbitrary single fppf
covers of any affine test scheme. -/
theorem isTrivial_fppf_of_isVectorGroupOfDimension {n : ℕ}
    (hV : RelativeRoot.IsVectorGroupOfDimension V n)
    (T : Over B) [IsAffine T.left] (U : Over T.left)
    [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom]
    (ξ : Cocycle ((GroupScheme.baseChange T.hom).obj V) U) : ξ.IsTrivial := by
  apply ξ.isTrivial_of_affine_fppf
  intro W _ _ _ _ ζ
  exact ζ.isTrivial_of_isVectorGroupOfDimension hV T W

/-- Actual retracts of finite vector groups have trivial cocycles on arbitrary
single fppf covers of affine test schemes. -/
theorem isTrivial_fppf_of_isFiniteVectorGroupRetract
    (hV : IsFiniteVectorGroupRetract V)
    (T : Over B) [IsAffine T.left] (U : Over T.left)
    [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom]
    (ξ : Cocycle ((GroupScheme.baseChange T.hom).obj V) U) : ξ.IsTrivial := by
  apply ξ.isTrivial_of_affine_fppf
  intro W _ _ _ _ ζ
  exact ζ.isTrivial_of_isFiniteVectorGroupRetract hV T W

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)} {U : Over (Spec R)}
  [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom]

/-- A supplied finite affine vector-quotient series kills cocycles on arbitrary
single fppf covers. -/
theorem isTrivial_fppf_of_hasAffineVectorSeries {n : ℕ}
    (hH : HasAffineVectorSeries n H) [IsAffineHom H.X.hom]
    (ξ : Cocycle H U) : ξ.IsTrivial :=
  (HasAffineVectorSeries.cocyclesVanish n H hH inferInstance).isTrivial_on_fppf U ξ

/-- Choose a cochain on the original single fppf cover for a group supplied
with a finite affine vector-quotient series. -/
def affineVectorSeriesFppfCochain {n : ℕ}
    (hH : HasAffineVectorSeries n H) [IsAffineHom H.X.hom]
    (ξ : Cocycle H U) : U ⟶ H.X :=
  Classical.choose (ξ.isTrivial_fppf_of_hasAffineVectorSeries hH)

/-- The chosen vector-series cochain satisfies the coboundary identity on all tests. -/
theorem affineVectorSeriesFppfCochain_spec {n : ℕ}
    (hH : HasAffineVectorSeries n H) [IsAffineHom H.X.hom]
    (ξ : Cocycle H U) {Z : Over (Spec R)} (a b : Z ⟶ U) :
    ξ.toFun a b = (a ≫ ξ.affineVectorSeriesFppfCochain hH) *
      (b ≫ ξ.affineVectorSeriesFppfCochain hH)⁻¹ :=
  Classical.choose_spec (ξ.isTrivial_fppf_of_hasAffineVectorSeries hH) a b

/-- A supplied split series is a special case of the finite vector-series result. -/
theorem isTrivial_fppf_of_hasSplitSeries {n : ℕ}
    (hH : RelativeRoot.HasSplitSeries n H) [IsAffineHom H.X.hom]
    (ξ : Cocycle H U) : ξ.IsTrivial :=
  ξ.isTrivial_fppf_of_hasAffineVectorSeries
    (HasAffineVectorSeries.of_hasSplitSeries hH)

end Cocycle

end Langlands.GroupScheme
