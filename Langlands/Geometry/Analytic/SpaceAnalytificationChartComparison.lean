import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceConstruction
import Langlands.Geometry.Analytic.AffineAnalytificationJointSurjectivity

/-! # The analytic quotient of a covering family of affine charts -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory SaturatedAtlasPresentation AffineAnalytification
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open ExistenceReduction

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}

/-- The maps of an analytification on any covering family of affine charts exhibit it
as their analytic quotient, with the actual analytified chart intersections. -/
def IsAnalytification.chartQuotient
    (hp : IsAnalytification K X Y p) (hX : IsSeparated X) (D : ChartData X) :
    QuotientData D where
  Y := Y
  π i := p (D.A i) (D.P i) (D.x i)
  etale i := hp.etale_map (D.P i) (D.x i) (D.etale i)
  surj y := by
    obtain ⟨B, _, _, Q, b, _, z, rfl⟩ := hp.jointly_surjective y
    let model (i : D.ι) := coverModel hX D Q b i
    obtain ⟨i, w, hw⟩ :=
      exists_mem_range_localizedHom K Q (fun i ↦ (model i).R) (fun i ↦ (model i).f)
        (fun prime ↦ by
          obtain ⟨i, hi⟩ := D.cover b prime
          exact ⟨i, hi (model i)⟩) z
    have square := hp.isPullback Q (D.P i) (model i).R (model i).f (model i).g
      b (D.x i) (model i).isPullback
    refine ⟨i, localizedSpaceFunctor.map (localizedHom K (D.P i) (model i).R (model i).g) w, ?_⟩
    rw [← TopCat.comp_app, ← Functor.map_comp, ← square.w, Functor.map_comp, TopCat.comp_app, hw]
  pullback i j _ _ _ Q f g h := hp.isPullback (D.P i) (D.P j) Q f g (D.x i) (D.x j) h

@[simp]
theorem IsAnalytification.chartQuotient_π
    (hp : IsAnalytification K X Y p) (hX : IsSeparated X) (D : ChartData X) (i : D.ι) :
    (hp.chartQuotient hX D).π i = p (D.A i) (D.P i) (D.x i) := rfl

/-- A compatible family of maps on the analytified charts descends uniquely to the quotient
if the target's Hom presheaf is an étale sheaf. Compatibility is tested on the actual
analytifications of the pairwise intersections. -/
theorem IsAnalytification.existsUnique_desc_chartQuotient
    (hp : IsAnalytification K X Y p) (hX : IsSeparated X) (D : ChartData X)
    {T : LocalizedCategory.{u, u, u} (K := K)}
    (hSheaf : Presieve.IsSheaf (etaleTopology Y) (etaleHomPresheaf Y T))
    (g : ∀ i, localized K (D.P i) ⟶ T)
    (hg : ∀ i j,
      let M := pointModel hX (D.P i) (D.P j) (D.x i) (D.x j)
      localizedHom K (D.P i) M.R M.f ≫ g i = localizedHom K (D.P j) M.R M.g ≫ g j) :
    ∃! F : Y ⟶ T, ∀ i, p (D.A i) (D.P i) (D.x i) ≫ F = g i := by
  let E := hp.chartQuotient hX D
  obtain ⟨F, hF⟩ := exists_glue_of_etale_cover hSheaf _ E.π E.etale E.surj g (by
    intro V i j a b hab
    let M := pointModel hX (D.P i) (D.P j) (D.x i) (D.x j)
    have square := E.pullback i j M.R M.f M.g M.isPullback
    obtain ⟨c, hca, hcb⟩ := square.exists_lift a b hab
    rw [← hca, ← hcb, Category.assoc, Category.assoc, hg i j])
  exact ⟨F, hF, fun F' hF' ↦
    hom_ext_of_etale_cover hSheaf _ E.π E.etale E.surj F' F
      (fun i ↦ (hF' i).trans (hF i).symm)⟩

end Langlands.Analytic.SpaceAnalytification
