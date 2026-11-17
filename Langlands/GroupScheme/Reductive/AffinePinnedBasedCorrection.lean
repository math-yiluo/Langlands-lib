import Langlands.GroupScheme.Reductive.AffinePinnedAffineAlignment
import Langlands.GroupScheme.Reductive.AffinePinnedSimultaneousNormalization

/-! # Affine etale charts with actual based inner correction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T U V : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- A target section corrects the actual comparison to full based data. -/
def HasBasedCorrection (e : Comparison f g) : Prop :=
  ∃ c : Over.mk (𝟙 T) ⟶ (N.groupOver g).X,
    ∃ d : BasedCoordinateIso (M.inclusionOver f) (N.inclusionOver g)
      M.rootDatum N.rootDatum M.basis N.basis,
      d.groupIso = e ≪≫ (N.groupOver g).innerIso c

private theorem basedCorrection_pullAlong_iff (e : Comparison f g) (q : U ⟶ T)
    {f' : U ⟶ M.base} {g' : U ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g') :
    HasBasedCorrection (pullComparisonAlong e q hf hg) ↔
      HasBasedCorrection (pullComparison e q) := by
  subst f'
  subst g'
  rw [pullComparisonAlong_rfl]

/-- A based correction is insensitive to the actual direct/iterated
normalized pullback identification. -/
theorem basedCorrection_pullComparison_comp_iff (e : Comparison f g)
    (q : U ⟶ T) (r : V ⟶ U) :
    HasBasedCorrection (pullComparison (pullComparison e q) r) ↔
      HasBasedCorrection (pullComparison e (r ≫ q)) := by
  rw [← basedCorrection_pullAlong_iff (pullComparison e q) r
    (Category.assoc r q f).symm (Category.assoc r q g).symm,
    ← pullComparisonAlong_rfl e q, pullComparisonAlong_comp,
    pullComparisonAlong_rfl]

/-- Above any point, an affine etale chart carries a target section giving
full based alignment for the exact pulled-back comparison. -/
theorem exists_affine_etale_basedCorrection (e : Comparison f g) (x : T) :
    ∃ (A : CommRingCat.{u}) (q : Spec A ⟶ T),
      Etale q ∧ x ∈ Set.range q ∧ HasBasedCorrection (pullComparison e q) := by
  obtain ⟨𝒰, h𝒰⟩ := hasEtaleBorelTorusNormalization e
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq x
  obtain ⟨c, hb, τ, hτ⟩ := h𝒰 j
  let E := pullComparison e (𝒰.f j) ≪≫
    (N.groupOver (𝒰.f j ≫ g)).innerIso c
  let a := affineBasedAlignment E τ hτ hb y
  let r := a.map
  let : Etale (𝒰.f j) := 𝒰.map_prop j
  let : IsOpenImmersion r := a.openImmersion
  refine ⟨a.ring, r ≫ 𝒰.f j, inferInstance, ?_, ?_⟩
  · exact ⟨a.point, by
      rw [Scheme.Hom.comp_apply, a.image_point]
      exact hy⟩
  · apply (basedCorrection_pullComparison_comp_iff e (𝒰.f j) r).mp
    refine ⟨N.pullBasePoint (𝒰.f j ≫ g) r c, a.data, ?_⟩
    have h := a.groupIso_eq
    dsimp only [E] at h
    rw [pullComparison_trans, pullComparison_inner] at h
    exact h

/-- An affine etale chart, a chosen point, and an actual based correction. -/
structure AffineBasedCorrectionChart (e : Comparison f g) (x : T) where
  ring : CommRingCat.{u}
  map : Spec ring ⟶ T
  etale : Etale map
  point : Spec ring
  image_point : map point = x
  section_ : Over.mk (𝟙 (Spec ring)) ⟶ (N.groupOver (map ≫ g)).X
  data : BasedCoordinateIso
    (M.inclusionOver (map ≫ f)) (N.inclusionOver (map ≫ g))
    M.rootDatum N.rootDatum M.basis N.basis
  groupIso_eq : data.groupIso =
    pullComparison e map ≪≫ (N.groupOver (map ≫ g)).innerIso section_

/-- Choose an affine etale based-correction chart above each point. -/
def affineBasedCorrectionChart (e : Comparison f g) (x : T) :
    AffineBasedCorrectionChart e x :=
  Classical.choice <| by
    obtain ⟨A, q, hq, ⟨y, hy⟩, c, d, hd⟩ :=
      exists_affine_etale_basedCorrection e x
    exact ⟨{
      ring := A
      map := q
      etale := hq
      point := y
      image_point := hy
      section_ := c
      data := d
      groupIso_eq := hd
    }⟩

/-- An arbitrary comparison has a covering family of affine etale charts
with actual based inner corrections. -/
def affineBasedCorrectionCover (e : Comparison f g) :
    Scheme.AffineCover.{u} @Etale T where
  I₀ := T
  X x := (affineBasedCorrectionChart e x).ring
  f x := (affineBasedCorrectionChart e x).map
  idx := id
  covers x := ⟨(affineBasedCorrectionChart e x).point,
    (affineBasedCorrectionChart e x).image_point⟩
  map_prop x := (affineBasedCorrectionChart e x).etale

/-- The corrected comparison on the selected chart preserves the exact
canonical ambient cocharacter. -/
theorem AffineBasedCorrectionChart.preservesCocharacter
    {e : Comparison f g} {x : T} (d : AffineBasedCorrectionChart e x) :
    PreservesCocharacter
      (pullComparison e d.map ≪≫ (N.groupOver (d.map ≫ g)).innerIso d.section_) := by
  have h := d.data.cocharacter_comp
  rw [d.groupIso_eq] at h
  exact h

end Langlands.GroupScheme.AffinePinnedModel
