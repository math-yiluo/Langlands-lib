import Langlands.Geometry.Analytic.QuasiEtaleHausdorffStabilityStatement
import Langlands.Geometry.Analytic.QuasiEtaleOverMorphismReduction
import Langlands.Geometry.Analytic.LocalizedQuasiEtaleLocality

/-! # Morphisms over `X` into a Hausdorff space quasi-étale over `X`
(Berkovich 1994, Lemma 3.1(ii)) -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A chart of an analytic domain `D` of `S` has the same chart domain, up to an isomorphism
compatible with the inclusions, as the underlying chart of `S`. -/
private theorem chartDomain_in_domain' {S : SaturatedAtlasPresentation.{u, v, v} K}
    (D : S.AnalyticDomain) (i : (S.domain D).presentation.atlas.Index) :
    ∃ e : localizationFunctor.obj ((S.domain D).domain ((S.domain D).chartDomain i)) ≅
      localizationFunctor.obj (S.domain (S.chartDomain i.val)),
      e.hom ≫ S.localizedDomainInclusion (S.chartDomain i.val) =
        (S.domain D).localizedDomainInclusion ((S.domain D).chartDomain i) ≫
          S.localizedDomainInclusion D :=
  exists_nestedChart_iso S D i.val i.property

/-- Let `D` be an analytic domain of `S` containing `y` on which `ψ` has a domain–étale
factorization. Then finitely many quasi-étale charts of `S` for `ψ` cover the trace on `D` of
a neighbourhood of `y`. -/
theorem exists_quasiEtaleCharts_of_hasDomainEtaleFactorization
    {S : SaturatedAtlasPresentation.{u, v, v} K} {Z : LocalizedCategory.{u, v, v} (K := K)}
    (ψ : localizationFunctor.obj S ⟶ Z) (D : S.AnalyticDomain) {y : S.presentation.space}
    (hyD : y ∈ D.carrier)
    (hD : HasDomainEtaleFactorization (S.localizedDomainInclusion D ≫ ψ)) :
    ∃ I : Set S.presentation.atlas.Index, I.Finite ∧ (∀ i ∈ I, S.IsQuasiEtaleChart ψ i) ∧
      ∃ O ∈ 𝓝 y, O ∩ D.carrier ⊆ ⋃ i ∈ I, range (S.presentation.atlas.chart i) := by
  obtain ⟨W, j, w, hj, hw, he⟩ := hD
  obtain ⟨W₀, hW₀⟩ := localizedObjectEquiv.surjective W
  change localizationFunctor.obj W₀ = W at hW₀
  subst W
  change localizationFunctor.obj (S.domain D) ⟶ localizationFunctor.obj W₀ at j
  let yD : D.carrier := ⟨y, hyD⟩
  obtain ⟨J, hJ, hJn, hJf⟩ :=
    IsAnalyticDomainEmbedding.exists_local_affinoidDomainEmbeddings
      (S := S.domain D) (W := W₀) hj yD
  obtain ⟨O, hO, hsub⟩ := (mem_nhds_subtype D.carrier yD _).mp hJn
  refine ⟨Subtype.val '' J, hJ.image _, ?_, O, hO, ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨e, hinc⟩ := chartDomain_in_domain' D i
    let ji := (S.domain D).localizedDomainInclusion ((S.domain D).chartDomain i)
    refine ⟨_, w, e.inv ≫ (ji ≫ j), hw, (hJf i hi).iso_comp e.symm, ?_⟩
    apply (cancel_epi e.hom).1
    calc
      _ = ji ≫ (j ≫ w) := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = e.hom ≫ S.localizedDomainInclusion (S.chartDomain i.val) ≫ ψ := by
        rw [he, ← Category.assoc ji, ← hinc, Category.assoc]
  · rintro x ⟨hxO, hxD⟩
    obtain ⟨i, hiJ, z, hz⟩ := mem_iUnion₂.mp (hsub (a := ⟨x, hxD⟩) hxO)
    exact mem_iUnion₂.mpr ⟨i.val, ⟨i, hiJ, rfl⟩, ⟨z, congrArg Subtype.val hz⟩⟩

/-- Let `g : Y ⟶ X` have pointed local domain–étale factorizations, and let `i` be a chart of
`Z` on which `f ≫ g` has a domain–étale factorization. Then the range of `i` is covered by
finitely many quasi-étale charts for `f`. -/
theorem exists_quasiEtaleCharts_cover_chart_of_comp
    {Z Y X : LocalizedCategory.{u, v, v} (K := K)} (f : Z ⟶ Y) (g : Y ⟶ X)
    (hg : HasLocalDomainEtaleFactorizations g)
    (i : (presentationOf Z).presentation.atlas.Index)
    (hi : HasDomainEtaleFactorization (domainι Z ((presentationOf Z).chartDomain i) ≫ f ≫ g)) :
    ∃ σ : Set (Set (presentationOf Z).presentation.space), σ.Finite ∧
      range ((presentationOf Z).presentation.atlas.chart i) ⊆ ⋃₀ σ ∧
      ∀ V ∈ σ, ∃ k : (presentationOf Z).presentation.atlas.Index,
        range ((presentationOf Z).presentation.atlas.chart k) = V ∧
          (presentationOf Z).IsQuasiEtaleChart f k := by
  classical
  let S := presentationOf Z
  have hlocal : ∀ x ∈ range (S.presentation.atlas.chart i),
      ∃ I : Set S.presentation.atlas.Index, I.Finite ∧ (∀ k ∈ I, S.IsQuasiEtaleChart f k) ∧
        ∃ O ∈ 𝓝 x, O ∩ range (S.presentation.atlas.chart i) ⊆
          ⋃ k ∈ I, range (S.presentation.atlas.chart k) := by
    intro x hx
    obtain ⟨C', hC'f, hC'n, hC'⟩ := hg (localizedSpaceFunctor.map f x)
    have hD : ∀ D ∈ C', ∃ I : Set S.presentation.atlas.Index, I.Finite ∧
        (∀ k ∈ I, S.IsQuasiEtaleChart f k) ∧ ∃ O ∈ 𝓝 x,
          O ∩ (S.chartDomain i ⊓ domainPreimage f D).carrier ⊆
            ⋃ k ∈ I, range (S.presentation.atlas.chart k) := by
      intro D hDC
      have hT : HasDomainEtaleFactorization
          ((domainι Z (S.chartDomain i ⊓ domainPreimage f D) ≫ f) ≫ g) := by
        rw [Category.assoc]
        exact hi.of_domain_le inf_le_left
      have hfac : HasDomainEtaleFactorization
          (domainι Z (S.chartDomain i ⊓ domainPreimage f D) ≫ f) := by
        refine hT.of_comp_of_factor (isAnalyticDomainEmbedding_domainι Y D)
          (k := domainOrderMap (inf_le_right :
              S.chartDomain i ⊓ domainPreimage f D ≤ domainPreimage f D) ≫
            domainPreimageMap f D) ?_ (hC' D hDC).2
        simp only [Category.assoc, domainPreimageMap_comp_inclusion,
          domainOrderMap_comp_inclusion_assoc]
      exact exists_quasiEtaleCharts_of_hasDomainEtaleFactorization f _
        ⟨hx, (hC' D hDC).1⟩ hfac
    choose! I hIf hIc O hO hOs using hD
    refine ⟨⋃ D ∈ C', I D, hC'f.biUnion hIf, fun k hk => ?_,
      (⋂ D ∈ C', O D) ∩ localizedSpaceFunctor.map f ⁻¹' (⋃ D ∈ C', D.carrier), ?_, ?_⟩
    · obtain ⟨D, hD, hkD⟩ := mem_iUnion₂.mp hk
      exact hIc D hD k hkD
    · exact inter_mem ((biInter_mem hC'f).mpr fun D hD => hO D hD)
        ((localizedSpaceFunctor.map f).hom.continuous.continuousAt.preimage_mem_nhds hC'n)
    · rintro y ⟨⟨hyO, hyF⟩, hyi⟩
      obtain ⟨D, hD, hyD⟩ := mem_iUnion₂.mp hyF
      obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp (hOs D hD ⟨mem_iInter₂.mp hyO D hD, hyi, hyD⟩)
      exact mem_iUnion₂.mpr ⟨k, mem_iUnion₂.mpr ⟨D, hD, hk⟩, hyk⟩
  choose! I hIf hIc O hO hOs using hlocal
  have hcpt : IsCompact (range (S.presentation.atlas.chart i)) :=
    isCompact_range (S.presentation.atlas.isEmbedding_chart i).continuous
  obtain ⟨t, hts, ht⟩ := hcpt.elim_nhds_subcover O hO
  refine ⟨(fun k => range (S.presentation.atlas.chart k)) '' ⋃ x ∈ (t : Set _), I x,
    (t.finite_toSet.biUnion fun x hx => hIf x (hts x hx)).image _, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (ht hy)
    obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp (hOs x (hts x hx) ⟨hyx, hy⟩)
    exact mem_sUnion.mpr ⟨_, ⟨k, mem_iUnion₂.mpr ⟨x, hx, hk⟩, rfl⟩, hyk⟩
  · rintro _ ⟨k, hk, rfl⟩
    obtain ⟨x, hx, hkx⟩ := mem_iUnion₂.mp hk
    exact ⟨k, rfl, hIc x (hts x hx) k hkx⟩

/-- If `g : Y ⟶ X` has pointed local domain–étale factorizations and `f ≫ g` is quasi-étale,
then `f` is quasi-étale. No hypothesis is made on the source `Z`. -/
theorem quasiEtale_of_comp_of_hasLocalDomainEtaleFactorizations
    {Z Y X : LocalizedCategory.{u, v, v} (K := K)} {f : Z ⟶ Y} {g : Y ⟶ X}
    (hg : HasLocalDomainEtaleFactorizations g) (hfg : quasiEtale (f ≫ g)) : quasiEtale f := by
  refine quasiEtale_of_forall_isLocalizedQuasiEtaleAt (S := presentationOf Z) f fun z => ?_
  obtain ⟨σ, hσ, hn, hs⟩ := isLocalizedQuasiEtaleAt_of_quasiEtale (S := presentationOf Z) hfg z
  refine IsLocalizedQuasiEtaleAt.of_cover σ hσ hn fun V hV => ?_
  obtain ⟨i, rfl, W, w, j, hw, hj, hjw⟩ := hs V hV
  exact exists_quasiEtaleCharts_cover_chart_of_comp f g hg i
    ⟨W, j, w, hj.isAnalyticDomainEmbedding, hw, hjw⟩

/-- Berkovich 1994, Lemma 3.1(ii), for a Hausdorff middle object: if `g : Y ⟶ X` and
`f ≫ g` are quasi-étale and the underlying space of `Y` is Hausdorff, then `f` is
quasi-étale. No hypothesis is made on `Z` or `X`. -/
theorem quasiEtale_of_comp_of_t2Space
    {Z Y X : LocalizedCategory.{u, v, v} (K := K)} {f : Z ⟶ Y} {g : Y ⟶ X}
    [T2Space (localizedSpaceFunctor.obj Y)] (hg : quasiEtale g) (hfg : quasiEtale (f ≫ g)) :
    quasiEtale f :=
  quasiEtale_of_comp_of_hasLocalDomainEtaleFactorizations
    (hasLocalDomainEtaleFactorizations_of_quasiEtale hg) hfg

/-- Proof of `QuasiEtaleHausdorffOverMorphismStatement` (Berkovich 1994, Lemma 3.1(ii), for a
Hausdorff middle object): if `g : Y ⟶ X` and `f ≫ g` are quasi-étale and the underlying space
of `Y` is Hausdorff, then `f` is quasi-étale. -/
theorem quasiEtaleHausdorffOverMorphism : QuasiEtaleHausdorffOverMorphismStatement.{u, v} K := by
  intro _ _ _ _ _ hY hg hfg
  exact quasiEtale_of_comp_of_t2Space hg hfg

end Langlands.Analytic.SaturatedAtlasPresentation
