import Langlands.Geometry.Analytic.PairChartPatch
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.RefinementGluing

/-! # Pullbacks are locally covered by charts inside pair-chart patches -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A chart of `P` lies in a pair-chart patch: its range is contained in the
patch `c.patch p q` of some pair chart `c` of the cospan `f`, `g`. -/
def InPairChartPatch {B U V P : LocalizedCategory.{u, v, v} (K := K)}
    (f : U ⟶ B) (g : V ⟶ B) (p : P ⟶ U) (q : P ⟶ V)
    (W : (presentationOf P).presentation.atlas.Index) : Prop :=
  ∃ c : PairChartData f g, range ((presentationOf P).presentation.atlas.chart W) ⊆
    (c.patch p q).carrier

/-- Around every point of a commutative square, the source is locally covered
by finitely many charts each lying in the patch of some pair chart; hence
every chart predicate that holds for all charts inside pair-chart patches
holds locally everywhere. -/
theorem isLocallyChartCovered_of_pairCharts {B U V P : LocalizedCategory.{u, v, v} (K := K)}
    {f : U ⟶ B} {g : V ⟶ B} {p : P ⟶ U} {q : P ⟶ V} (w : p ≫ f = q ≫ g)
    (Q : (presentationOf P).presentation.atlas.Index → Prop)
    (hQ : ∀ (c : PairChartData f g) (W : (presentationOf P).presentation.atlas.Index),
      range ((presentationOf P).presentation.atlas.chart W) ⊆ (c.patch p q).carrier → Q W)
    (y : (presentationOf P).presentation.space) :
    (presentationOf P).IsLocallyChartCovered Q univ y := by
  classical
  have hw : ∀ z, localizedSpaceFunctor.map f (localizedSpaceFunctor.map p z) =
      localizedSpaceFunctor.map g (localizedSpaceFunctor.map q z) := by
    intro z
    rw [← TopCat.comp_app, ← Functor.map_comp, w, Functor.map_comp, TopCat.comp_app]
  obtain ⟨K₀, hK₀fin, hK₀, NB, hNB, hKcov⟩ :=
    isLocallyChartCovered_of_mem_nhds (T := presentationOf B)
      (Filter.univ_mem (f := 𝓝 (localizedSpaceFunctor.map f (localizedSpaceFunctor.map p y))))
  have hU : ∀ k ∈ K₀, (presentationOf U).IsLocallyChartCovered (fun _ => True)
      (domainPreimage f ((presentationOf B).chartDomain k)).carrier
      (localizedSpaceFunctor.map p y) :=
    fun k hk => isLocallyChartCovered_analyticDomain _ (hK₀ k hk).1
  have hV : ∀ k ∈ K₀, (presentationOf V).IsLocallyChartCovered (fun _ => True)
      (domainPreimage g ((presentationOf B).chartDomain k)).carrier
      (localizedSpaceFunctor.map q y) := by
    intro k hk
    apply isLocallyChartCovered_analyticDomain
    exact Eq.mp (congrArg (fun x => x ∈ range ((presentationOf B).presentation.atlas.chart k))
      (hw y)) (hK₀ k hk).1
  choose MU hMUfin hMU NU hNU hMUcov using hU
  choose MV hMVfin hMV NV hNV hMVcov using hV
  have : Finite K₀ := hK₀fin.to_subtype
  have : ∀ k : K₀, Finite ↥(MU k.1 k.2 ×ˢ MV k.1 k.2) :=
    fun k => ((hMUfin k.1 k.2).prod (hMVfin k.1 k.2)).to_subtype
  let ι := Σ k : K₀, ↥(MU k.1 k.2 ×ˢ MV k.1 k.2)
  let c : ι → PairChartData f g := fun i =>
    { left := i.2.1.1
      right := i.2.1.2
      base := i.1.1
      left_mapsTo := fun _ hx => (hMU i.1.1 i.1.2 i.2.1.1 i.2.2.1).2.1 hx
      right_mapsTo := fun _ hx => (hMV i.1.1 i.1.2 i.2.1.2 i.2.2.2).2.1 hx }
  have hpc : Continuous (localizedSpaceFunctor.map p) := (localizedSpaceFunctor.map p).hom.continuous
  have hqc : Continuous (localizedSpaceFunctor.map q) := (localizedSpaceFunctor.map q).hom.continuous
  have hfc : Continuous (localizedSpaceFunctor.map f) := (localizedSpaceFunctor.map f).hom.continuous
  let N₀ : Set (presentationOf P).presentation.space :=
    (localizedSpaceFunctor.map p ⁻¹' ⋂ k : K₀, NU k.1 k.2) ∩
      (localizedSpaceFunctor.map q ⁻¹' ⋂ k : K₀, NV k.1 k.2) ∩
      (localizedSpaceFunctor.map p ⁻¹' (localizedSpaceFunctor.map f ⁻¹' NB))
  have hN₀ : N₀ ∈ 𝓝 y := by
    refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
    · exact hpc.continuousAt.preimage_mem_nhds
        (Filter.iInter_mem.2 fun k => hNU k.1 k.2)
    · exact hqc.continuousAt.preimage_mem_nhds
        (Filter.iInter_mem.2 fun k => hNV k.1 k.2)
    · exact hpc.continuousAt.preimage_mem_nhds (hfc.continuousAt.preimage_mem_nhds hNB)
  refine isLocallyChartCovered_of_cover (T := presentationOf P) (ι := ι)
    (Zs := fun i => ((c i).patch p q).carrier) (fun _ => subset_univ _) hN₀ ?_ ?_
  · rintro z ⟨-, ⟨hzU, hzV⟩, hzB⟩
    have hzB' : localizedSpaceFunctor.map f (localizedSpaceFunctor.map p z) ∈
        ⋃ k ∈ K₀, range ((presentationOf B).presentation.atlas.chart k) := hKcov ⟨trivial, hzB⟩
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 hzB'
    have hzU' := hMUcov k hk ⟨hzk, mem_iInter.1 hzU ⟨k, hk⟩⟩
    obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.1 hzU'
    have hzk' : localizedSpaceFunctor.map g (localizedSpaceFunctor.map q z) ∈
        range ((presentationOf B).presentation.atlas.chart k) :=
      Eq.mp (congrArg (fun x => x ∈ range ((presentationOf B).presentation.atlas.chart k))
        (hw z)) hzk
    have hzV' := hMVcov k hk ⟨hzk', mem_iInter.1 hzV ⟨k, hk⟩⟩
    obtain ⟨n, hn, hzn⟩ := mem_iUnion₂.1 hzV'
    exact mem_iUnion.2 ⟨⟨⟨k, hk⟩, ⟨(m, n), hm, hn⟩⟩, hzm, hzn⟩
  · intro i
    apply IsLocallyChartCovered.of_subset_pred
    · exact isLocallyChartCovered_analyticDomain _
        ⟨(hMU i.1.1 i.1.2 i.2.1.1 i.2.2.1).1, (hMV i.1.1 i.1.2 i.2.1.2 i.2.2.2).1⟩
    · exact fun W hW => hQ (c i) W hW

/-- Every point of the source of a commutative square is locally covered by
charts lying in pair-chart patches. -/
theorem isLocallyChartCovered_inPairChartPatch {B U V P : LocalizedCategory.{u, v, v} (K := K)}
    {f : U ⟶ B} {g : V ⟶ B} {p : P ⟶ U} {q : P ⟶ V} (w : p ≫ f = q ≫ g)
    (y : (presentationOf P).presentation.space) :
    (presentationOf P).IsLocallyChartCovered (InPairChartPatch f g p q) univ y :=
  isLocallyChartCovered_of_pairCharts w _ (fun c _ hW => ⟨c, hW⟩) y

end Langlands.Analytic.SaturatedAtlasPresentation
