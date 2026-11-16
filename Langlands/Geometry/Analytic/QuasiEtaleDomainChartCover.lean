import Langlands.Geometry.Analytic.QuasiEtaleCompactSiteCover
import Langlands.Geometry.Analytic.DomainEtaleFactorizations

/-! # Finite compact domain charts with retained étale envelopes -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter Topology
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Local quasi-étale charts retain a single étale envelope for each chart. -/
theorem IsQuasiEtale.exists_local_domainEtale_charts
    {A B : AffinoidAtlasPresentation.{u, v, v} K}
    {g : ofSaturation A ⟶ ofSaturation B} (hg : IsQuasiEtale g) (y : A.space) :
    ∃ σ : Set (Set A.space), σ.Finite ∧ ⋃₀ σ ∈ 𝓝 y ∧
      ∀ V ∈ σ, ∃ i : (ofSaturation A).presentation.atlas.Index,
        Set.range ((ofSaturation A).presentation.atlas.chart i) = V ∧
        HasDomainEtaleFactorization ((ofSaturation A).localizedDomainInclusion
          ((ofSaturation A).chartDomain i) ≫ localizationFunctor.map g) := by
  obtain ⟨σ, hf, hn, hs⟩ := hg y
  refine ⟨σ, hf, hn, fun V hV => ?_⟩
  obtain ⟨i, hi, W, f, j, hf, hj, ht⟩ := hs V hV
  exact ⟨i, hi, W, j, f, hj.isAnalyticDomainEmbedding, hf, ht⟩

/-- Compact selection preserves the domain-étale factorization witnesses. -/
theorem IsQuasiEtale.exists_finite_domainEtale_chart_cover
    {A B : AffinoidAtlasPresentation.{u, v, v} K}
    {g : ofSaturation A ⟶ ofSaturation B} (hg : IsQuasiEtale g)
    [CompactSpace A.space] :
    ∃ s : Finset (ofSaturation A).presentation.atlas.Index,
      (∀ i ∈ s, HasDomainEtaleFactorization
        ((ofSaturation A).localizedDomainInclusion
          ((ofSaturation A).chartDomain i) ≫ localizationFunctor.map g)) ∧
      ∀ y : A.space, ∃ i ∈ s,
        y ∈ Set.range ((ofSaturation A).presentation.atlas.chart i) := by
  classical
  choose σ hf hn hs using hg.exists_local_domainEtale_charts
  obtain ⟨t, _, ht⟩ :=
    isCompact_univ.elim_nhds_subcover (fun x => ⋃₀ σ x) (fun x _ => hn x)
  let δ : Set (Set A.space) := ⋃ x ∈ (t : Set A.space), σ x
  have hδ : δ.Finite := t.finite_toSet.biUnion (fun x _ => hf x)
  have hgood : ∀ V : δ, ∃ i : (ofSaturation A).presentation.atlas.Index,
      Set.range ((ofSaturation A).presentation.atlas.chart i) = V.val ∧
        HasDomainEtaleFactorization ((ofSaturation A).localizedDomainInclusion
          ((ofSaturation A).chartDomain i) ≫ localizationFunctor.map g) := by
    intro V
    obtain ⟨x, _, hx⟩ := Set.mem_iUnion₂.mp V.property
    exact hs x V.val hx
  choose idx hidx hfactor using hgood
  let : Fintype δ := hδ.fintype
  refine ⟨Finset.univ.image idx, ?_, ?_⟩
  · intro i hi
    obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hi
    exact hfactor V
  · intro y
    obtain ⟨x, hx, V, hV, hyV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    let W : δ := ⟨V, Set.mem_iUnion₂.mpr ⟨x, hx, hV⟩⟩
    refine ⟨idx W, Finset.mem_image.mpr ⟨W, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (hidx W).symm ▸ hyV

variable {X : LocalizedCategory.{u, v, v} (K := K)}

/-- A finite compact chart cover with actual ambient domains and retained
domain-étale factorizations of the structure maps. -/
structure FiniteCompactDomainChartCover (U : QuasiEtaleSite X)
    extends FiniteCompactChartCover U where
  domain : Index → (presentationOf U.left).AnalyticDomain
  domainIso : ∀ i, (obj i).left ≅ domainObj U.left (domain i)
  domainIso_hom_inclusion : ∀ i,
    (domainIso i).hom ≫ domainι U.left (domain i) = (arrow i).left
  factorization : ∀ i, HasDomainEtaleFactorization (obj i).hom

namespace FiniteCompactDomainChartCover

variable {U : QuasiEtaleSite X} (C : FiniteCompactDomainChartCover U)

/-- The actual finite chart-family presieve. -/
def presieve : Presieve U := C.toFiniteCompactChartCover.presieve

theorem mem_quasiEtalePrecoverage : C.presieve ∈ quasiEtalePrecoverage X U :=
  C.toFiniteCompactChartCover.mem_quasiEtalePrecoverage

theorem generate_mem_quasiEtaleTopology :
    Sieve.generate C.presieve ∈ quasiEtaleTopology X U :=
  C.toFiniteCompactChartCover.generate_mem_quasiEtaleTopology

/-- The cover arrows are actual analytic-domain embeddings into the target. -/
theorem arrow_isAnalyticDomainEmbedding (i : C.Index) :
    IsAnalyticDomainEmbedding (C.arrow i).left :=
  ⟨C.domain i, C.domainIso i, (C.domainIso_hom_inclusion i).symm⟩

/-- The structure map of each actual ambient domain retains an étale envelope. -/
theorem domain_factorization (i : C.Index) :
    HasDomainEtaleFactorization (domainι U.left (C.domain i) ≫ U.hom) := by
  have h := (C.factorization i).iso_comp (C.domainIso i).symm
  have hw : (C.obj i).hom =
      (C.domainIso i).hom ≫ (domainι U.left (C.domain i) ≫ U.hom) := by
    rw [← Category.assoc, C.domainIso_hom_inclusion]
    simpa using (C.arrow i).w.symm
  rw [hw, Iso.symm_hom, Iso.inv_hom_id_assoc] at h
  exact h

/-- Restriction to any further domain keeps the selected étale envelope. -/
theorem domain_restriction_factorization (i : C.Index)
    (D : (presentationOf (domainObj U.left (C.domain i))).AnalyticDomain) :
    HasDomainEtaleFactorization
      (domainι (domainObj U.left (C.domain i)) D ≫
        (domainι U.left (C.domain i) ≫ U.hom)) :=
  (C.domain_factorization i).domainι_comp D

end FiniteCompactDomainChartCover

/-- Every compact-underlying quasi-étale site object admits a finite compact
chart cover with actual ambient-domain witnesses and retained étale envelopes. -/
theorem exists_finiteCompactDomainChartCover (U : QuasiEtaleSite X)
    [CompactSpace (localizedSpaceFunctor.obj U.left)] :
    Nonempty (FiniteCompactDomainChartCover U) := by
  classical
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := U.prop
  let ex : localizationFunctor.obj (ofSaturation A) ≅ U.left :=
    Arrow.leftFunc.mapIso e
  let ey : localizationFunctor.obj (ofSaturation B) ≅ X :=
    Arrow.rightFunc.mapIso e
  let : CompactSpace A.space :=
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso ex)).symm.compactSpace
  obtain ⟨s, hfactor, hcover⟩ := hg.exists_finite_domainEtale_chart_cover
  let V : s → QuasiEtaleSite X := fun i =>
    MorphismProperty.Over.mk ⊤
      (((ofSaturation A).localizedDomainInclusion
        ((ofSaturation A).chartDomain i.val) ≫ localizationFunctor.map g) ≫ ey.hom)
      (((hfactor i.val i.property).comp_iso ey).quasiEtale)
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
  let C : FiniteCompactChartCover U :=
    { Index := s
      finite := inferInstance
      obj := V
      arrow := f
      compact := fun i => isCompactSpace_chartDomainObj (ofSaturation A) i.val
      chart := fun i => chartDomainFullChart (ofSaturation A) i.val
      chart_surjective := fun i => chartDomainFullChart_surjective (ofSaturation A) i.val
      jointly_surjective := by
        intro x
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
        exact ha }
  refine ⟨{ toFiniteCompactChartCover := C
            domain := fun i => domainPreimage ex.inv ((ofSaturation A).chartDomain i.val)
            domainIso := fun i => domainImageIso ex ((ofSaturation A).chartDomain i.val)
            domainIso_hom_inclusion := ?_
            factorization := fun i => (hfactor i.val i.property).comp_iso ey }⟩
  intro i
  exact domainImageIso_hom_inclusion ex ((ofSaturation A).chartDomain i.val)

end Langlands.Analytic.SaturatedAtlasPresentation
