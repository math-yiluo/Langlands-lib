import Langlands.Geometry.Analytic.QuasiEtaleFiniteChartCover

/-! # Finite compact chart covers as actual quasi-étale site covers -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter Topology
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}

/-- A finite cover by compact quasi-étale objects, each of which has a full chart. -/
structure FiniteCompactChartCover (U : QuasiEtaleSite X) where
  Index : Type v
  finite : Finite Index
  obj : Index → QuasiEtaleSite X
  arrow : ∀ i, obj i ⟶ U
  compact : ∀ i, IsCompactSpace (obj i).left
  chart : ∀ i, (localizedObjectEquiv.symm (obj i).left).presentation.atlas.Index
  chart_surjective : ∀ i, Function.Surjective
    ((localizedObjectEquiv.symm (obj i).left).presentation.atlas.chart (chart i))
  jointly_surjective : ∀ x : localizedSpaceFunctor.obj U.left,
    ∃ (i : Index) (y : localizedSpaceFunctor.obj (obj i).left),
      localizedSpaceFunctor.map (arrow i).left y = x

namespace FiniteCompactChartCover

variable {U : QuasiEtaleSite X} (C : FiniteCompactChartCover U)

/-- The actual presieve consisting of the selected finite family. -/
def presieve : Presieve U := Presieve.ofArrows C.obj C.arrow

/-- The full charts and joint surjectivity give the defining covering condition. -/
theorem mem_quasiEtalePrecoverage : C.presieve ∈ quasiEtalePrecoverage X U := by
  classical
  let := C.finite
  let T : C.Index → Set (localizedSpaceFunctor.obj U.left) := fun i =>
    localizedSpaceFunctor.map (C.arrow i).left ''
      Set.range ((localizedObjectEquiv.symm (C.obj i).left).presentation.atlas.chart
        (C.chart i))
  have hT : ⋃₀ Set.range T = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := C.jointly_surjective x
    exact Set.mem_sUnion.mpr ⟨T i, ⟨i, rfl⟩,
      ⟨y, C.chart_surjective i y, hy⟩⟩
  intro x
  refine ⟨Set.range T, Set.finite_range T, ?_, ?_⟩
  · rw [hT]
    exact Filter.univ_mem
  · rintro _ ⟨i, rfl⟩
    exact ⟨C.obj i, C.arrow i, C.chart i, Presieve.ofArrows.mk i, rfl⟩

/-- The selected family generates a covering sieve in the actual topology. -/
theorem generate_mem_quasiEtaleTopology :
    Sieve.generate C.presieve ∈ quasiEtaleTopology X U :=
  SaturatedAtlasPresentation.generate_mem_quasiEtaleTopology C.mem_quasiEtalePrecoverage

end FiniteCompactChartCover

/-- Every quasi-étale site object with compact underlying space has a finite
cover by actual compact chart objects in the defining precoverage. -/
theorem exists_finiteCompactChartCover (U : QuasiEtaleSite X)
    [CompactSpace (localizedSpaceFunctor.obj U.left)] :
    Nonempty (FiniteCompactChartCover U) := by
  classical
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := U.prop
  let ex : localizationFunctor.obj (ofSaturation A) ≅ U.left :=
    Arrow.leftFunc.mapIso e
  let ey : localizationFunctor.obj (ofSaturation B) ≅ X :=
    Arrow.rightFunc.mapIso e
  let : CompactSpace A.space :=
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso ex)).symm.compactSpace
  obtain ⟨s, hqe, hcover⟩ := hg.exists_finite_quasiEtale_chart_cover
  let V : s → QuasiEtaleSite X := fun i =>
    MorphismProperty.Over.mk ⊤
      (((ofSaturation A).localizedDomainInclusion
        ((ofSaturation A).chartDomain i.val) ≫ localizationFunctor.map g) ≫ ey.hom)
      (((quasiEtale (K := K)).cancel_right_of_respectsIso _ ey.hom).mpr
        (hqe i.val i.property))
  let f : ∀ i, V i ⟶ U := fun i =>
    MorphismProperty.Over.homMk
      ((ofSaturation A).localizedDomainInclusion ((ofSaturation A).chartDomain i.val) ≫
        ex.hom) (by
          let j := (ofSaturation A).localizedDomainInclusion
            ((ofSaturation A).chartDomain i.val)
          have hw : ex.hom ≫ U.hom = localizationFunctor.map g ≫ ey.hom := e.hom.w
          exact (Category.assoc j ex.hom U.hom).trans
            ((congrArg (fun k => j ≫ k) hw).trans
              (Category.assoc j (localizationFunctor.map g) ey.hom).symm))
  refine ⟨⟨s, inferInstance, V, f, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    exact isCompactSpace_chartDomainObj (ofSaturation A) i.val
  · intro i
    exact chartDomainFullChart (ofSaturation A) i.val
  · intro i
    exact chartDomainFullChart_surjective (ofSaturation A) i.val
  · intro x
    obtain ⟨a, ha⟩ := (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso ex)).surjective x
    obtain ⟨i, hi, hai⟩ := hcover a
    refine ⟨⟨i, hi⟩, ⟨a, hai⟩, ?_⟩
    change localizedSpaceFunctor.map
      ((ofSaturation A).localizedDomainInclusion ((ofSaturation A).chartDomain i) ≫
        ex.hom) ⟨a, hai⟩ = x
    rw [Functor.map_comp]
    change localizedSpaceFunctor.map ex.hom
      (localizedSpaceFunctor.map
        ((ofSaturation A).localizedDomainInclusion ((ofSaturation A).chartDomain i))
          ⟨a, hai⟩) = x
    rw [localizedSpaceFunctor_map_localizedDomainInclusion]
    exact ha

end Langlands.Analytic.SaturatedAtlasPresentation
