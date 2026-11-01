import Langlands.Geometry.Analytic.ChosenAtlasDomainTransport
import Langlands.Geometry.Analytic.OriginalDomainPullbacks

/-! # Actual bounded presentation transport of original domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Restriction of the actual base homeomorphism to an original domain and its image. -/
def isoOriginalDomainHomeomorph (e : A ≅ B) (S : A.atlas.OriginalChartDomain) :
    S ≃ₜ isoOriginalDomain e S :=
  (isoHomeomorph e).image (S : Set A.space)

@[simp]
theorem isoOriginalDomainHomeomorph_apply_val (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) (x : S) :
    (isoOriginalDomainHomeomorph e S x).val = e.hom.baseMap x.val := rfl

@[simp]
theorem isoOriginalDomainHomeomorph_symm_apply_val (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) (y : isoOriginalDomain e S) :
    ((isoOriginalDomainHomeomorph e S).symm y).val = e.inv.baseMap y.val := rfl

/-- Every selected target chart of the restricted forward arrow lies in the image. -/
theorem isoOriginalDomainMap_chart_subset (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain)
    (c : (A.originalDomainPresentation S).atlas.Index) :
    Set.range (B.atlas.chart ((A.originalDomainInclusion S ≫ e.hom).indexMap c)) ⊆
      isoOriginalDomain e S := by
  change Set.range (B.atlas.chart (e.hom.indexMap c.val)) ⊆
    isoHomeomorph e '' (S : Set A.space)
  rw [← isoHomeomorph_image_chart]
  exact Set.image_mono c.property

/-- The actual domain map retains the entire original chosen bounded pullback. -/
def isoOriginalDomainMap (e : A ≅ B) (S : A.atlas.OriginalChartDomain) :
    A.originalDomainPresentation S ⟶ B.originalDomainPresentation (isoOriginalDomain e S) :=
  (A.originalDomainInclusion S ≫ e.hom).factorOriginalDomain
    (isoOriginalDomain e S) (isoOriginalDomainMap_chart_subset e S)

/-- Every selected chart of the restricted inverse lies in the original source domain. -/
theorem isoOriginalDomainInverse_chart_subset (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain)
    (c : B.atlas.SubspaceChart (isoOriginalDomain e S).carrier) :
    Set.range (A.atlas.chart
      ((B.originalDomainInclusion (isoOriginalDomain e S) ≫ e.inv).indexMap c)) ⊆ S := by
  change Set.range (A.atlas.chart (e.inv.indexMap c.val)) ⊆ (S : Set A.space)
  calc
    Set.range (A.atlas.chart (e.inv.indexMap c.val)) =
        isoHomeomorph e.symm '' Set.range (B.atlas.chart c.val) :=
      (isoHomeomorph_image_chart e.symm c.val).symm
    _ ⊆ isoHomeomorph e.symm '' (isoOriginalDomain e S : Set B.space) :=
      Set.image_mono c.property
    _ = (S : Set A.space) := (isoHomeomorph e).toEquiv.symm_image_image _

/-- The actual inverse domain map retains the original inverse bounded pullbacks. -/
def isoOriginalDomainInverse (e : A ≅ B) (S : A.atlas.OriginalChartDomain) :
    B.originalDomainPresentation (isoOriginalDomain e S) ⟶ A.originalDomainPresentation S :=
  (B.originalDomainInclusion (isoOriginalDomain e S) ≫ e.inv).factorOriginalDomain
    S (isoOriginalDomainInverse_chart_subset e S)

@[simp]
theorem isoOriginalDomainMap_apply_val (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) (x : S) :
    ((isoOriginalDomainMap e S).baseMap x).val = e.hom.baseMap x.val := rfl

@[simp]
theorem isoOriginalDomainInverse_apply_val (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) (y : isoOriginalDomain e S) :
    ((isoOriginalDomainInverse e S).baseMap y).val = e.inv.baseMap y.val := rfl

@[simp]
theorem isoOriginalDomainMap_index_val (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain)
    (c : (A.originalDomainPresentation S).atlas.Index) :
    ((isoOriginalDomainMap e S).indexMap c).val = e.hom.indexMap c.val := rfl

@[simp]
theorem isoOriginalDomainInverse_index_val (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain)
    (c : (B.originalDomainPresentation (isoOriginalDomain e S)).atlas.Index) :
    ((isoOriginalDomainInverse e S).indexMap c).val = e.inv.indexMap c.val := rfl

@[simp]
theorem isoOriginalDomainMap_pullback (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain)
    (c : (A.originalDomainPresentation S).atlas.Index) :
    (isoOriginalDomainMap e S).pullback c = e.hom.pullback c.val := rfl

@[simp]
theorem isoOriginalDomainInverse_pullback (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain)
    (c : (B.originalDomainPresentation (isoOriginalDomain e S)).atlas.Index) :
    (isoOriginalDomainInverse e S).pullback c = e.inv.pullback c.val := rfl

/-- Forward transport commutes with the actual ambient chosen inclusions. -/
@[simp]
theorem isoOriginalDomainMap_inclusion (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) :
    isoOriginalDomainMap e S ≫ B.originalDomainInclusion (isoOriginalDomain e S) =
      A.originalDomainInclusion S ≫ e.hom :=
  Hom.factorOriginalDomain_inclusion _ _ _

/-- Inverse transport commutes with the actual ambient chosen inclusions. -/
@[simp]
theorem isoOriginalDomainInverse_inclusion (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) :
    isoOriginalDomainInverse e S ≫ A.originalDomainInclusion S =
      B.originalDomainInclusion (isoOriginalDomain e S) ≫ e.inv :=
  Hom.factorOriginalDomain_inclusion _ _ _

/-- Full forward/inverse laws follow by cancelling the complete bounded inclusion. -/
@[simp]
theorem isoOriginalDomainMap_inverse_id (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) :
    isoOriginalDomainMap e S ≫ isoOriginalDomainInverse e S =
      𝟙 (A.originalDomainPresentation S) := by
  apply (cancel_mono (A.originalDomainInclusion S)).mp
  rw [Category.assoc, isoOriginalDomainInverse_inclusion, ← Category.assoc,
    isoOriginalDomainMap_inclusion, Category.assoc, e.hom_inv_id,
    Category.comp_id, Category.id_comp]

@[simp]
theorem isoOriginalDomainInverse_map_id (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) :
    isoOriginalDomainInverse e S ≫ isoOriginalDomainMap e S =
      𝟙 (B.originalDomainPresentation (isoOriginalDomain e S)) := by
  apply (cancel_mono (B.originalDomainInclusion (isoOriginalDomain e S))).mp
  rw [Category.assoc, isoOriginalDomainMap_inclusion, ← Category.assoc,
    isoOriginalDomainInverse_inclusion, Category.assoc, e.inv_hom_id,
    Category.comp_id, Category.id_comp]

/-- Realizing an original domain commutes with transport by a full chosen isomorphism. -/
def isoOriginalDomainPresentation (e : A ≅ B) (S : A.atlas.OriginalChartDomain) :
    A.originalDomainPresentation S ≅ B.originalDomainPresentation (isoOriginalDomain e S) where
  hom := isoOriginalDomainMap e S
  inv := isoOriginalDomainInverse e S
  hom_inv_id := isoOriginalDomainMap_inverse_id e S
  inv_hom_id := isoOriginalDomainInverse_map_id e S

/-- The presentation isomorphism has precisely the actual restricted homeomorphism. -/
theorem isoOriginalDomainPresentation_homeomorph (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) :
    isoHomeomorph (isoOriginalDomainPresentation e S) = isoOriginalDomainHomeomorph e S := by
  ext x
  rfl

/-- Actual image subsets preserve every original-domain inclusion. -/
theorem isoOriginalDomain_mono (e : A ≅ B)
    {S T : A.atlas.OriginalChartDomain} (h : S ≤ T) :
    isoOriginalDomain e S ≤ isoOriginalDomain e T :=
  Set.image_mono h

/-- Complete forward transport is natural under every original-domain inclusion. -/
theorem isoOriginalDomainMap_naturality (e : A ≅ B)
    {S T : A.atlas.OriginalChartDomain} (h : S ≤ T) :
    A.originalDomainMap h ≫ isoOriginalDomainMap e T =
      isoOriginalDomainMap e S ≫
        B.originalDomainMap (isoOriginalDomain_mono e h) := by
  apply (cancel_mono (B.originalDomainInclusion (isoOriginalDomain e T))).mp
  simp only [Category.assoc, isoOriginalDomainMap_inclusion, originalDomainMap_inclusion]
  rw [← Category.assoc, A.originalDomainMap_inclusion]

/-- Complete inverse transport is also natural under every domain inclusion. -/
theorem isoOriginalDomainInverse_naturality (e : A ≅ B)
    {S T : A.atlas.OriginalChartDomain} (h : S ≤ T) :
    B.originalDomainMap (isoOriginalDomain_mono e h) ≫
        isoOriginalDomainInverse e T =
      isoOriginalDomainInverse e S ≫ A.originalDomainMap h := by
  apply (cancel_mono (A.originalDomainInclusion T)).mp
  simp only [Category.assoc, isoOriginalDomainInverse_inclusion, originalDomainMap_inclusion]
  rw [← Category.assoc, B.originalDomainMap_inclusion]

/-- A natural isomorphism of the actual bounded presentation diagrams. -/
def isoOriginalDomainPresentationNatIso (e : A ≅ B) :
    A.originalDomainFunctor ≅
      (isoOriginalDomainEquivalence e).functor ⋙ B.originalDomainFunctor :=
  NatIso.ofComponents (isoOriginalDomainPresentation e)
    (fun f => isoOriginalDomainMap_naturality e (leOfHom f))

end Langlands.Analytic.AffinoidAtlasPresentation
