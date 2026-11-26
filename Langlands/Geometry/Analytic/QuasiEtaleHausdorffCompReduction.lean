import Langlands.Geometry.Analytic.QuasiEtaleCompReduction
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.QuasiEtaleHausdorffCompReductionStatement

/-! # Composition of quasi-étale morphisms with Hausdorff sources -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A domain–étale factorization of `f` on an analytic domain `D` can be
shrunk around a point `y` of `D`: on `D ∩ O`, for an open neighbourhood `O`
of `y`, the restriction of `f` has a domain–étale factorization whose étale
envelope is Hausdorff. -/
theorem HasDomainEtaleFactorization.exists_t2Space_inf_openDomain
    {A B : LocalizedCategory.{u, v, v} (K := K)} {f : A ⟶ B}
    {D : (presentationOf A).AnalyticDomain}
    (hD : HasDomainEtaleFactorization (domainι A D ≫ f))
    (y : localizedSpaceFunctor.obj A) (hy : y ∈ D.carrier) :
    ∃ (O : Set (localizedSpaceFunctor.obj A)) (hO : IsOpen O), y ∈ O ∧
      ∃ (W : LocalizedCategory.{u, v, v} (K := K))
        (j : domainObj A (D ⊓ (presentationOf A).openDomain O hO) ⟶ W) (w : W ⟶ B),
        T2Space (localizedSpaceFunctor.obj W) ∧ IsAnalyticDomainEmbedding j ∧ etale w ∧
          j ≫ w = domainι A (D ⊓ (presentationOf A).openDomain O hO) ≫ f := by
  obtain ⟨W, j, w, hj, hw, hjw⟩ := hD
  let yD : localizedSpaceFunctor.obj (domainObj A D) := ⟨y, hy⟩
  obtain ⟨N, hN, hNt⟩ :=
    (presentationOf W).presentation.atlas.locallyHausdorff (localizedSpaceFunctor.map j yD)
  let H : Set (localizedSpaceFunctor.obj W) := interior N
  have hH : IsOpen H := isOpen_interior
  have hjH : localizedSpaceFunctor.map j yD ∈ H := mem_interior_iff_mem_nhds.mpr hN
  have hHt : T2Space H :=
    @Topology.IsEmbedding.t2Space _ _ _ _ hNt _ (Topology.IsEmbedding.inclusion interior_subset)
  have hpre : localizedSpaceFunctor.map j ⁻¹' H ∈ 𝓝 yD :=
    (localizedSpaceFunctor.map j).hom.continuous.continuousAt.preimage_mem_nhds
      (hH.mem_nhds hjH)
  obtain ⟨O₀, hO₀, hsub⟩ := (mem_nhds_subtype D.carrier yD _).mp hpre
  let O := interior O₀
  have hO : IsOpen O := isOpen_interior
  have hyO : y ∈ O := mem_interior_iff_mem_nhds.mpr hO₀
  let D' := D ⊓ (presentationOf A).openDomain O hO
  let m : domainObj A D' ⟶ domainObj A D := domainOrderMap (inf_le_left : D' ≤ D)
  have hmD : m ≫ domainι A D = domainι A D' := domainOrderMap_comp_inclusion _
  have hm : IsAnalyticDomainEmbedding m := by
    apply IsAnalyticDomainEmbedding.of_comp_domainι
    rw [hmD]
    exact isAnalyticDomainEmbedding_domainι A D'
  have hmpt : ∀ x : localizedSpaceFunctor.obj (domainObj A D'),
      (localizedSpaceFunctor.map m x).val = x.val := by
    intro x
    have h := congrArg (fun φ => localizedSpaceFunctor.map φ x) hmD
    simp only [Functor.map_comp, TopCat.comp_app, domainι_apply] at h
    exact h
  let H' := (presentationOf W).openDomain H hH
  have hmem : ∀ x, localizedSpaceFunctor.map (m ≫ j) x ∈ H'.carrier := by
    intro x
    rw [Functor.map_comp, TopCat.comp_app]
    apply hsub
    change (localizedSpaceFunctor.map m x).val ∈ O₀
    rw [hmpt]
    exact interior_subset x.property.2
  let n : domainObj A D' ⟶ domainObj W H' := domainLift H' (m ≫ j) hmem
  have hn : n ≫ domainι W H' = m ≫ j := domainLift_comp _ _ _
  have hna : IsAnalyticDomainEmbedding n := by
    apply IsAnalyticDomainEmbedding.of_comp_domainι
    rw [hn]
    exact hm.comp hj
  have hWt : T2Space (localizedSpaceFunctor.obj (domainObj W H')) := hHt
  refine ⟨O, hO, hyO, domainObj W H', n, domainι W H' ≫ w, hWt, hna,
    etale_comp (etaleOpenDomainStatement W H hH) hw, ?_⟩
  rw [← Category.assoc, hn, Category.assoc, hjw, ← Category.assoc, hmD]

/-- Local domain–étale factorizations can be chosen with Hausdorff étale
envelopes. -/
theorem HasLocalDomainEtaleFactorizations.exists_t2Space_envelopes
    {A B : LocalizedCategory.{u, v, v} (K := K)} {f : A ⟶ B}
    (h : HasLocalDomainEtaleFactorizations f) (y : localizedSpaceFunctor.obj A) :
    ∃ C : Set (presentationOf A).AnalyticDomain, C.Finite ∧
      (⋃ D ∈ C, D.carrier) ∈ 𝓝 y ∧
      ∀ D ∈ C, y ∈ D.carrier ∧
        ∃ (W : LocalizedCategory.{u, v, v} (K := K)) (j : domainObj A D ⟶ W) (w : W ⟶ B),
          T2Space (localizedSpaceFunctor.obj W) ∧ IsAnalyticDomainEmbedding j ∧ etale w ∧
            j ≫ w = domainι A D ≫ f := by
  classical
  obtain ⟨C, hC, hn, hD⟩ := h y
  have hshrink : ∀ D ∈ C, ∃ (O : Set (localizedSpaceFunctor.obj A)) (hO : IsOpen O), y ∈ O ∧
      ∃ (W : LocalizedCategory.{u, v, v} (K := K))
        (j : domainObj A (D ⊓ (presentationOf A).openDomain O hO) ⟶ W) (w : W ⟶ B),
        T2Space (localizedSpaceFunctor.obj W) ∧ IsAnalyticDomainEmbedding j ∧ etale w ∧
          j ≫ w = domainι A (D ⊓ (presentationOf A).openDomain O hO) ≫ f :=
    fun D hDC => (hD D hDC).2.exists_t2Space_inf_openDomain y (hD D hDC).1
  choose O hO hyO hfac using hshrink
  let : Finite C := hC.to_subtype
  let Φ : C → (presentationOf A).AnalyticDomain := fun D =>
    D.val ⊓ (presentationOf A).openDomain (O D.val D.property) (hO D.val D.property)
  refine ⟨range Φ, finite_range Φ, ?_, ?_⟩
  · have hOn : (⋂ D : C, O D.val D.property) ∈ 𝓝 y :=
      Filter.iInter_mem.mpr fun D => (hO D.val D.property).mem_nhds (hyO D.val D.property)
    refine Filter.mem_of_superset (Filter.inter_mem hn hOn) ?_
    rintro x ⟨hx, hOx⟩
    obtain ⟨D, hDC, hxD⟩ := mem_iUnion₂.mp hx
    have hxO := mem_iInter.mp hOx (⟨D, hDC⟩ : C)
    exact mem_iUnion₂.mpr ⟨Φ ⟨D, hDC⟩, ⟨⟨D, hDC⟩, rfl⟩, ⟨hxD, hxO⟩⟩
  · rintro _ ⟨D, rfl⟩
    exact ⟨⟨(hD D.val D.property).1, hyO D.val D.property⟩, hfac D.val D.property⟩

/-- The local step of the composition with a Hausdorff envelope for the first
factorization: if `f` restricted to `D` factors through an analytic domain of
a Hausdorff space `W` étale over the target, and `g` restricted to `E` has a
domain–étale factorization, then `f ≫ g` restricted to `D ∩ f⁻¹(E)` has local
domain–étale factorizations. -/
theorem hasLocalDomainEtaleFactorizations_inf_domainPreimage_of_t2Space
    (hB : EtaleDomainQuasiEtaleStatement.{u, v} K)
    {A B C : LocalizedCategory.{u, v, v} (K := K)} {f : A ⟶ B} {g : B ⟶ C}
    {D : (presentationOf A).AnalyticDomain} {E : (presentationOf B).AnalyticDomain}
    {W : LocalizedCategory.{u, v, v} (K := K)} [T2Space (localizedSpaceFunctor.obj W)]
    {j : domainObj A D ⟶ W} {w : W ⟶ B} (hj : IsAnalyticDomainEmbedding j) (hw : etale w)
    (hjw : j ≫ w = domainι A D ≫ f)
    (hE : HasDomainEtaleFactorization (domainι B E ≫ g)) :
    HasLocalDomainEtaleFactorizations (domainι A (D ⊓ domainPreimage f E) ≫ f ≫ g) := by
  obtain ⟨W', j', w', ⟨R, e', rfl⟩, hw', hjw'⟩ := hE
  let P := domainPreimage w E
  let p := domainPreimageMap w E
  have hp : etale (p ≫ e'.hom) := etale_comp (etale_domainPreimageMap w E hw) (etale_of_isIso _)
  have hPt : T2Space (localizedSpaceFunctor.obj (domainObj W P)) := by
    refine T2Space.of_injective_continuous
      (f := fun x => localizedSpaceFunctor.map (domainι W P) x) ?_
      (localizedSpaceFunctor.map (domainι W P)).hom.continuous
    intro a b hab
    simp only [domainι_apply] at hab
    exact Subtype.ext hab
  have hP : HasLocalDomainEtaleFactorizations (domainι W P ≫ w ≫ g) := by
    have h1 := (hasLocalDomainEtaleFactorizations_of_quasiEtale (hB R _ hp)).comp_etale hw'
    have h2 : ((p ≫ e'.hom) ≫ domainι W' R) ≫ w' = domainι W P ≫ w ≫ g := by
      rw [Category.assoc, Category.assoc, ← Category.assoc e'.hom, hjw',
        domainPreimageMap_comp_inclusion_assoc]
    rwa [h2] at h1
  let G := D ⊓ domainPreimage f E
  let m : domainObj A G ⟶ domainObj A D := domainOrderMap (inf_le_left : G ≤ D)
  have hm : IsAnalyticDomainEmbedding m := by
    apply IsAnalyticDomainEmbedding.of_comp_domainι
    rw [domainOrderMap_comp_inclusion]
    exact isAnalyticDomainEmbedding_domainι A G
  have hmem : ∀ x, localizedSpaceFunctor.map (m ≫ j) x ∈ P.carrier := by
    intro x
    change localizedSpaceFunctor.map w (localizedSpaceFunctor.map (m ≫ j) x) ∈ E.carrier
    rw [← TopCat.comp_app, ← Functor.map_comp, Category.assoc, hjw, ← Category.assoc,
      domainOrderMap_comp_inclusion, Functor.map_comp, TopCat.comp_app, domainι_apply]
    exact x.property.2
  let n : domainObj A G ⟶ domainObj W P := domainLift P (m ≫ j) hmem
  have hn : n ≫ domainι W P = m ≫ j := domainLift_comp _ _ _
  have hna : IsAnalyticDomainEmbedding n := by
    apply IsAnalyticDomainEmbedding.of_comp_domainι
    rw [hn]
    exact hm.comp hj
  have h3 := hP.analyticDomainEmbedding_comp hna
  have hmD : m ≫ domainι A D = domainι A G := domainOrderMap_comp_inclusion _
  have h4 : n ≫ domainι W P ≫ w ≫ g = domainι A G ≫ f ≫ g := by
    rw [← Category.assoc n, hn, Category.assoc, reassoc_of% hjw, ← Category.assoc m, hmD]
  rwa [h4] at h3

/-- Quasi-étale morphisms with Hausdorff sources compose, given that an étale
morphism into an analytic domain followed by the inclusion of the domain is
quasi-étale (`EtaleDomainQuasiEtaleStatement`). -/
theorem quasiEtale_comp_of_t2Space (hB : EtaleDomainQuasiEtaleStatement.{u, v} K)
    {A B C : LocalizedCategory.{u, v, v} (K := K)} (f : A ⟶ B) (g : B ⟶ C)
    [T2Space (localizedSpaceFunctor.obj A)] [T2Space (localizedSpaceFunctor.obj B)]
    (hf : quasiEtale f) (hg : quasiEtale g) : quasiEtale (f ≫ g) := by
  apply HasLocalDomainEtaleFactorizations.quasiEtale
  apply HasLocalDomainEtaleFactorizations.of_domain_cover
  intro y
  obtain ⟨CD, hCD, hnD, hD⟩ :=
    (hasLocalDomainEtaleFactorizations_of_quasiEtale hf).exists_t2Space_envelopes y
  obtain ⟨CE, hCE, hnE, hE⟩ :=
    hasLocalDomainEtaleFactorizations_of_quasiEtale hg (localizedSpaceFunctor.map f y)
  refine ⟨Set.image2 (fun D E => D ⊓ domainPreimage f E) CD CE, hCD.image2 _ hCE, ?_, ?_⟩
  · refine Filter.mem_of_superset (Filter.inter_mem hnD
      ((localizedSpaceFunctor.map f).hom.continuous.continuousAt.preimage_mem_nhds hnE)) ?_
    rintro x ⟨hxD, hxE⟩
    obtain ⟨D, hDC, hxD⟩ := mem_iUnion₂.mp hxD
    obtain ⟨E, hEC, hxE⟩ := mem_iUnion₂.mp hxE
    exact mem_iUnion₂.mpr ⟨_, ⟨D, hDC, E, hEC, rfl⟩, ⟨hxD, hxE⟩⟩
  · rintro _ ⟨D, hDC, E, hEC, rfl⟩
    obtain ⟨hyD, W, j, w, hWt, hj, hw, hjw⟩ := hD D hDC
    obtain ⟨hyE, hgE⟩ := hE E hEC
    exact ⟨⟨hyD, hyE⟩,
      hasLocalDomainEtaleFactorizations_inf_domainPreimage_of_t2Space hB hj hw hjw hgE⟩

/-- Proof of `QuasiEtaleHausdorffCompReductionStatement`: from
`EtaleDomainQuasiEtaleStatement`, quasi-étale morphisms with Hausdorff sources
compose (`QuasiEtaleHausdorffCompStatement`). -/
theorem quasiEtaleHausdorffCompReduction : QuasiEtaleHausdorffCompReductionStatement.{u, v} K := by
  intro hB A B C f g hA hB' hf hg
  have := hA
  have := hB'
  exact quasiEtale_comp_of_t2Space hB f g hf hg

end Langlands.Analytic.SaturatedAtlasPresentation
