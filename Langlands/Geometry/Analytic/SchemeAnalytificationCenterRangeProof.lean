import Langlands.Geometry.Analytic.SchemeAnalytificationBasicOpen

/-! # The range of analytification charts -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification.CenterRange

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

set_option backward.isDefEq.respectTransparency false in
/-- Basic-open membership of the center is nonvanishing of the corresponding section. -/
theorem localCenter_mem_basicOpen (U : X.affineOpens) (g : Γ(X, U.val))
    (z : LocalSpace K f U) :
    localCenter K f U z ∈ X.basicOpen g ↔
      AffineAnalytification.pointSeminorm K (chartPresentation K f U) z
        (basicOpenGenerator f U g) ≠ 0 := by
  let Y := (U : X.Opens).toScheme
  let q : Y := Y.isoSpec.inv (localCenterPoint K f U z)
  have hpre : (U : X.Opens).ι ⁻¹ᵁ X.basicOpen g =
      Y.basicOpen ((U : X.Opens).topIso.inv g) := by
    rw [← (U : X.Opens).ι_image_basicOpen_topIso_inv g,
      (U : X.Opens).ι.preimage_image_eq]
  change q ∈ (U : X.Opens).ι ⁻¹ᵁ X.basicOpen g ↔ _
  rw [hpre, ← Y.toSpecΓ_preimage_basicOpen]
  change Y.isoSpec.hom (Y.isoSpec.inv (localCenterPoint K f U z)) ∈
    PrimeSpectrum.basicOpen (basicOpenGenerator f U g) ↔ _
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  exact AffineAnalytification.center_mem_basicOpen K (chartPresentation K f U) z
    (basicOpenGenerator f U g)

/-- The principal-open range input for center-range arguments. -/
def BasicOpenRangeData : Prop :=
  ∀ (U : X.affineOpens) (g : Γ(X, U.val)),
    Set.range (localMap K f (X.affineBasicOpen_le g)) =
      localCenter K f U ⁻¹' (X.basicOpen g : Set X)

/-- An affine localization-range formula gives the needed principal-open range. -/
theorem range_localMap_basicOpen_of_nonvanishing (U : X.affineOpens) (g : Γ(X, U.val))
    (hrange : Set.range (localMap K f (X.affineBasicOpen_le g)) =
      {z | AffineAnalytification.pointSeminorm K (chartPresentation K f U) z
        (basicOpenGenerator f U g) ≠ 0}) :
    Set.range (localMap K f (X.affineBasicOpen_le g)) =
      localCenter K f U ⁻¹' (X.basicOpen g : Set X) := by
  rw [hrange]
  ext z
  exact (localCenter_mem_basicOpen K f U g z).symm

/-- Principal neighborhoods suffice for the global affine-chart range identity. -/
theorem range_ι (hbasic : BasicOpenRangeData K f) (U : X.affineOpens) :
    center K f ⁻¹' ((U : X.Opens) : Set X) = Set.range (ι K f U) := by
  ext z
  constructor
  · intro hz
    obtain ⟨V, y, rfl⟩ := exists_ι K f z
    change localCenter K f V y ∈ (U : X.Opens) at hz
    obtain ⟨g, hgU, hyg⟩ := V.property.exists_basicOpen_le
      ⟨localCenter K f V y, hz⟩ (center_ι_mem K f V y)
    have hy : y ∈ Set.range (localMap K f (X.affineBasicOpen_le g)) := by
      rw [hbasic V g]
      exact hyg
    obtain ⟨w, hw⟩ := hy
    refine ⟨localMap K f (show ((X.affineBasicOpen g) : X.Opens) ≤ U from hgU) w, ?_⟩
    rw [ι_localMap, ← ι_localMap K f (X.affineBasicOpen_le g), hw]
  · rintro ⟨w, rfl⟩
    exact center_ι_mem K f U w

/-- Principal neighborhoods and composition suffice for every affine restriction range. -/
theorem range_localMap (hbasic : BasicOpenRangeData K f)
    (hcomp : ∀ {U V W : X.affineOpens} (hVU : (V : X.Opens) ≤ U)
      (hWV : (W : X.Opens) ≤ V) (y : LocalSpace K f W),
      localMap K f hVU (localMap K f hWV y) = localMap K f (hWV.trans hVU) y)
    {U V : X.affineOpens} (hVU : (V : X.Opens) ≤ U) :
    Set.range (localMap K f hVU) = localCenter K f U ⁻¹' ((V : X.Opens) : Set X) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change localCenter K f U (localMap K f hVU w) ∈ (V : X.Opens)
    rw [localCenter_localMap]
    exact center_ι_mem K f V w
  · intro hz
    obtain ⟨g, hgV, hzg⟩ := U.property.exists_basicOpen_le
      ⟨localCenter K f U z, hz⟩ (center_ι_mem K f U z)
    have hz' : z ∈ Set.range (localMap K f (X.affineBasicOpen_le g)) := by
      rw [hbasic U g]
      exact hzg
    obtain ⟨w, hw⟩ := hz'
    refine ⟨localMap K f (show ((X.affineBasicOpen g) : X.Opens) ≤ V from hgV) w, ?_⟩
    rw [hcomp]
    exact hw

end Langlands.Analytic.SchemeAnalytification.CenterRange
