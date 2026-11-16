import Langlands.GroupScheme.RelativeUnipotent.VectorBundleBaseChangeCocycle
import Langlands.GroupScheme.RelativeUnipotent.AffineCocycleReduction
import Langlands.GroupScheme.CocycleAffineRefinement

/-! # Cocycle vanishing for finite vector-bundle series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeUnipotent

variable {S : Scheme.{u}} [IsAffine S]

/-- An affine group with a supplied finite vector-bundle series has vanishing
cocycles after every affine test base change. -/
theorem HasVectorBundleSeries.cocyclesVanish :
    ∀ (n : ℕ) (H : GroupScheme S), HasVectorBundleSeries n H →
      IsAffineHom H.X.hom → AffineCocycle.CocyclesVanish H
  | 0, _, h, _ => AffineCocycle.cocyclesVanish_of_range_id_eq_bot h
  | n + 1, H, ⟨K, V, j, q, hj, _, _, ⟨_, _, _, hjq⟩, hV, hK⟩, _ => by
      have : IsClosedImmersion j.hom.hom.left := hj
      have : Mono j.hom.hom := Over.mono_of_mono_left _
      have : IsAffineHom K.X.hom := by
        rw [← Over.w j.hom.hom]
        infer_instance
      have hKv := HasVectorBundleSeries.cocyclesVanish n K hK this
      have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
      have : IsAffineHom V.X.hom := hV.1
      have : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
      obtain ⟨σ, hσ⟩ := AffineCocycle.exists_section j q hjq hKv
      exact AffineCocycle.cocyclesVanish_of_section j q hjq σ hσ
        (fun T _ U _ _ _ ξ =>
          AffineVectorBundleCocycle.cocycle_isTrivial_baseChange T.hom hV ξ) hKv

/-- The length of the supplied finite vector-bundle series need not be chosen. -/
theorem HasFiniteVectorBundleSeries.cocyclesVanish {H : GroupScheme S}
    (hH : HasFiniteVectorBundleSeries H) [IsAffineHom H.X.hom] :
    AffineCocycle.CocyclesVanish H := by
  obtain ⟨n, hn⟩ := hH
  exact HasVectorBundleSeries.cocyclesVanish n H hn inferInstance

end RelativeUnipotent

namespace Cocycle

open RelativeUnipotent

variable {S : Scheme.{u}} [IsAffine S] {H : GroupScheme S}
  [IsAffineHom H.X.hom] (hH : HasFiniteVectorBundleSeries H)

include hH

/-- The original group's cocycles vanish on affine flat surjective covers. -/
theorem isTrivial_of_hasFiniteVectorBundleSeries
    {U : Over S} [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (ξ : Cocycle H U) : ξ.IsTrivial :=
  AffineCocycle.cocycle_isTrivial hH.cocyclesVanish ξ

/-- A supplied vector-bundle series also kills cocycles on arbitrary single
fppf covers of the affine base. -/
theorem isTrivial_fppf_of_hasFiniteVectorBundleSeries
    {U : Over S} [Flat U.hom] [Surjective U.hom]
    [LocallyOfFinitePresentation U.hom] (ξ : Cocycle H U) : ξ.IsTrivial := by
  apply ξ.isTrivial_of_affine_fppf
  intro W _ _ _ _ ζ
  exact ζ.isTrivial_of_hasFiniteVectorBundleSeries hH

/-- The same original-cover conclusion holds after every affine test base change. -/
theorem isTrivial_fppf_baseChange_of_hasFiniteVectorBundleSeries
    (T : Over S) [IsAffine T.left] {U : Over T.left}
    [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom]
    (ξ : Cocycle ((GroupScheme.baseChange T.hom).obj H) U) : ξ.IsTrivial := by
  apply ξ.isTrivial_of_affine_fppf
  intro W _ _ _ _ ζ
  exact hH.cocyclesVanish T W ζ

/-- Choose one cochain on the original fppf cover from the supplied series. -/
def vectorBundleSeriesFppfCochain
    {U : Over S} [Flat U.hom] [Surjective U.hom]
    [LocallyOfFinitePresentation U.hom] (ξ : Cocycle H U) : U ⟶ H.X :=
  Classical.choose (ξ.isTrivial_fppf_of_hasFiniteVectorBundleSeries hH)

/-- The chosen cochain satisfies the coboundary identity on all test schemes. -/
theorem vectorBundleSeriesFppfCochain_spec
    {U : Over S} [Flat U.hom] [Surjective U.hom]
    [LocallyOfFinitePresentation U.hom] (ξ : Cocycle H U)
    {Z : Over S} (a b : Z ⟶ U) :
    ξ.toFun a b = (a ≫ ξ.vectorBundleSeriesFppfCochain hH) *
      (b ≫ ξ.vectorBundleSeriesFppfCochain hH)⁻¹ :=
  Classical.choose_spec (ξ.isTrivial_fppf_of_hasFiniteVectorBundleSeries hH) a b

end Cocycle

end Langlands.GroupScheme
