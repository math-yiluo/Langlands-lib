import Langlands.Geometry.Analytic.QuasiEtaleCompactProbeTopology
import Langlands.Geometry.Analytic.QuasiEtaleGeometricPointCones
import Langlands.Geometry.Analytic.QuasiEtaleSiteFieldPointLift
import Langlands.Geometry.Analytic.CommonPointField.Proof

/-! # Geometric points for the compact-probe quasi-étale topology -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleSite

open _root_.CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}

/-- Every underlying point of a quasi-étale site object is in the image of a compact
Hausdorff probe. Use a chart containing the point from the local quasi-étale factorization. -/
theorem exists_compactProbe_over_point (U : QuasiEtaleSite X)
    (x : localizedSpaceFunctor.obj U.left) :
    ∃ (C : QuasiEtaleSite X) (f : C ⟶ U), IsCompactSpace C.left ∧
      x ∈ Set.range (localizedSpaceFunctor.map f.left) := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := U.prop
  let eU : localizationFunctor.obj (ofSaturation A) ≅ U.left := Arrow.leftFunc.mapIso e
  let eX : localizationFunctor.obj (ofSaturation B) ≅ X := Arrow.rightFunc.mapIso e
  obtain ⟨a, ha⟩ := (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eU)).surjective x
  obtain ⟨σ, _, hn, hcharts⟩ := hg.exists_local_quasiEtale_charts a
  obtain ⟨V, hV, haV⟩ := Set.mem_sUnion.mp (mem_of_mem_nhds hn)
  obtain ⟨i, hi, hqe⟩ := hcharts V hV
  let S := ofSaturation A
  let j := S.localizedDomainInclusion (S.chartDomain i)
  let C : QuasiEtaleSite X := MorphismProperty.Over.mk ⊤ ((j ≫ localizationFunctor.map g) ≫ eX.hom)
    (((quasiEtale (K := K)).cancel_right_of_respectsIso _ eX.hom).mpr hqe)
  let f : C ⟶ U := MorphismProperty.Over.homMk (j ≫ eU.hom) (by
    have hw : eU.hom ≫ U.hom = localizationFunctor.map g ≫ eX.hom := e.hom.w
    change (j ≫ eU.hom) ≫ U.hom = (j ≫ localizationFunctor.map g) ≫ eX.hom
    exact (Category.assoc _ _ _).trans
      ((congrArg (j ≫ ·) hw).trans (Category.assoc _ _ _).symm))
  have hai : a ∈ Set.range (S.presentation.atlas.chart i) := hi.symm ▸ haV
  let t : localizedSpaceFunctor.obj C.left := ⟨a, hai⟩
  refine ⟨C, f, isCompactSpace_chartDomainObj S i, ⟨t, ?_⟩⟩
  change localizedSpaceFunctor.map (j ≫ eU.hom) t = x
  rw [Functor.map_comp]
  change localizedSpaceFunctor.map eU.hom (localizedSpaceFunctor.map j t) = x
  rw [localizedSpaceFunctor_map_localizedDomainInclusion]
  exact ha

/-- A compact-probe covering sieve is jointly surjective on underlying points.
Apply the covering test to a compact chart through the chosen point. -/
theorem exists_mem_range_of_mem_compactProbeTopology {U : QuasiEtaleSite X} {S : Sieve U}
    (hS : S ∈ compactProbeQuasiEtaleTopology X U) (x : localizedSpaceFunctor.obj U.left) :
    ∃ (V : QuasiEtaleSite X) (f : V ⟶ U), S f ∧ x ∈ Set.range (localizedSpaceFunctor.map f.left) := by
  obtain ⟨C, g, hC, y, hy⟩ := exists_compactProbe_over_point U x
  obtain ⟨n, V, f, _, hf, hit⟩ := hS g hC
  obtain ⟨i, z, hz⟩ := hit y
  refine ⟨V i, f i ≫ g, hf i, z, ?_⟩
  change localizedSpaceFunctor.map ((f i).left ≫ g.left) z = x
  rw [Functor.map_comp]
  change localizedSpaceFunctor.map g.left (localizedSpaceFunctor.map (f i).left z) = x
  exact (congrArg (localizedSpaceFunctor.map g.left) hz).trans hy

variable (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
  [NormedAlgebra K L]

/-- Every field-valued point over a complete algebraically closed extension defines a
site point of the compact-probe topology. Refinements and equalization make its fibre
cofiltered. Joint surjectivity follows by lifting the full point through a covering arrow. -/
theorem compactProbePointAxioms (x : (localizedFieldPointFunctor L).obj X) :
    OverSite.PointAxioms quasiEtale L (compactProbeQuasiEtaleTopology X) x := by
  refine ⟨pointFibre_isCofiltered_of_geometry L geometricPointRefinement
    geometricPointEqualization x, ?_⟩
  intro U S hS p
  obtain ⟨V, f, hf, hy⟩ := exists_mem_range_of_mem_compactProbeTopology hS
    ((localizedFieldPointProjection L).app U.left p.1).down
  obtain ⟨q, hq⟩ := geometricPointImageLift K L X U V f p.1 hy
  have hqx : (localizedFieldPointFunctor L).map V.hom q = x := by
    rw [← MorphismProperty.Over.w f, Functor.map_comp_apply, hq]
    exact p.2
  exact ⟨V, f, hf, ⟨q, hqx⟩, Subtype.ext hq⟩

/-- The compact-probe site point with fibre the lifts of `x` to quasi-étale objects. -/
abbrev compactProbeGeometricPoint (x : (localizedFieldPointFunctor L).obj X) :
    (compactProbeQuasiEtaleTopology X).Point.{max u (v + 1) uL} :=
  OverSite.toPoint quasiEtale L (compactProbeQuasiEtaleTopology X) x (compactProbePointAxioms L x)

/-- If the field realizes all points of the base, the same field realizes every point of
every quasi-étale object. Lift along the structure map at the prescribed underlying point. -/
theorem surjective_fieldPointProjection_of_base
    (hX : Function.Surjective ((localizedFieldPointProjection L).app X)) (U : QuasiEtaleSite X) :
    Function.Surjective ((localizedFieldPointProjection L).app U.left) := by
  intro y
  obtain ⟨x, hx⟩ := hX (ULift.up (localizedSpaceFunctor.map U.hom y.down))
  have he : quasiEtale (U.hom ≫ 𝟙 X) := (Category.comp_id U.hom).symm ▸ U.prop
  obtain ⟨p, hp, _⟩ := pointedFieldPointLift_of_quasiEtale_comp (L := L) he x y.down
    (congrArg ULift.down hx).symm
  exact ⟨p, ULift.ext hp⟩

end Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleSite
