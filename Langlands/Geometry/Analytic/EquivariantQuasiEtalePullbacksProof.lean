import Langlands.Geometry.Analytic.CompactQuasiEtaleDiagonal
import Langlands.Geometry.Analytic.EquivariantSitePullbacksReduction
import Langlands.Geometry.Analytic.LocalizedCompactNeighborhoods
import Langlands.Geometry.Analytic.QuasiEtaleCommonProduct
import Langlands.Geometry.Analytic.QuasiEtaleCompReduction
import Langlands.Geometry.Analytic.QuasiEtaleOverMorphismReduction
import Langlands.Geometry.Analytic.RecognizedDomainSaturationSite
import Langlands.Geometry.Analytic.RestrictionSiteMorphismReduction

/-! # Analytic pullbacks in the equivariant quasi-étale site -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B U X P : LocalizedCategory.{u, v, v} (K := K)}

/-- Right cancellation for quasi-étale maps with Hausdorff sources.
On finite domain neighborhoods it is the local graph factorization. -/
theorem quasiEtale_of_over_of_t2Space
    [T2Space (localizedSpaceFunctor.obj A)] [T2Space (localizedSpaceFunctor.obj U)]
    {f : A ⟶ U} {h : U ⟶ X} (hh : quasiEtale h) (hf : quasiEtale (f ≫ h)) :
    quasiEtale f := by
  apply HasLocalDomainEtaleFactorizations.quasiEtale
  intro z
  obtain ⟨C, hc, hn, hC⟩ := hasLocalDomainEtaleFactorizations_of_quasiEtale hf z
  obtain ⟨D, hd, hm, hD⟩ := hasLocalDomainEtaleFactorizations_of_quasiEtale hh
    (localizedSpaceFunctor.map f z)
  let E (p : (presentationOf A).AnalyticDomain × (presentationOf U).AnalyticDomain) :=
    p.1 ⊓ domainPreimage f p.2
  refine ⟨E '' (C ×ˢ D), (hc.prod hd).image _, ?_, ?_⟩
  · refine Filter.mem_of_superset (Filter.inter_mem hn
      ((localizedSpaceFunctor.map f).hom.continuous.continuousAt.preimage_mem_nhds hm)) ?_
    rintro y ⟨hyC, hyD⟩
    obtain ⟨S, hS, hyS⟩ := mem_iUnion₂.mp hyC
    obtain ⟨T, hT, hyT⟩ := mem_iUnion₂.mp (Set.mem_preimage.mp hyD)
    exact mem_iUnion₂.mpr ⟨E (S, T), ⟨(S, T), ⟨hS, hT⟩, rfl⟩, hyS, hyT⟩
  · rintro _ ⟨⟨S, T⟩, ⟨hS, hT⟩, rfl⟩
    refine ⟨⟨(hC S hS).1, (hD T hT).1⟩, ?_⟩
    have hS' : HasDomainEtaleFactorization ((domainι A (E (S, T)) ≫ f) ≫ h) := by
      rw [Category.assoc]
      exact (hC S hS).2.of_domain_le inf_le_left
    exact hS'.of_comp_of_factor (isAnalyticDomainEmbedding_domainι U T)
      (k := domainOrderMap (inf_le_right : E (S, T) ≤ domainPreimage f T) ≫ domainPreimageMap f T)
      (by simp only [Category.assoc, domainPreimageMap_comp_inclusion,
        domainOrderMap_comp_inclusion_assoc]) (hD T hT).2

private theorem exists_compact_domain_nhds (U : LocalizedCategory.{u, v, v} (K := K))
    [T2Space (localizedSpaceFunctor.obj U)] (x : localizedSpaceFunctor.obj U) :
    ∃ D : (presentationOf U).AnalyticDomain, IsCompactSpace (domainObj U D) ∧ D.carrier ∈ 𝓝 x := by
  classical
  let a := (presentationOf U).presentation.atlas
  obtain ⟨σ, hf, hσ, _, hn⟩ := a.isNet_chartFamily.1 x
  choose i hi using fun S : σ => hσ S.property
  let : Finite σ := hf.to_subtype
  have hUnion : ⋃ S : σ, range (a.chart (i S)) = ⋃₀ σ := by
    simp only [hi, Set.sUnion_eq_iUnion, Set.iUnion_subtype]
  let : T2Space (presentationOf U).presentation.space :=
    inferInstanceAs (T2Space (localizedSpaceFunctor.obj U))
  let D : (presentationOf U).AnalyticDomain :=
    ⟨⋃₀ σ, a.isOriginalChartDomain_of_finite_chart_cover _ i hUnion⟩
  have hD := (presentationOf U).isCompactDomain_of_eq_iUnion D i hUnion.symm
  exact ⟨D, ⟨isCompact_iff_compactSpace.mp hD.1, hD.2⟩, hn⟩

private theorem common_of_pullback_over_compact
    [T2Space (localizedSpaceFunctor.obj A)] [T2Space (localizedSpaceFunctor.obj B)]
    {f : A ⟶ U} {g : B ⟶ U} {b : U ⟶ X} {p : P ⟶ A} {q : P ⟶ B}
    (h : IsPullback p q f g) (hU : IsCompactSpace U) (hb : quasiEtale b)
    (hf : quasiEtale (f ≫ b)) (hg : quasiEtale (g ≫ b)) :
    HasLocalDomainEtaleFactorizations (q ≫ g ≫ b) := by
  let C := localizedQuasiEtalePullback (f ≫ b) (g ≫ b) hf
  let Q := localizedQuasiEtalePullback b b hb
  have hC := IsPullback.of_isLimit C.2
  have hQ := IsPullback.of_isLimit Q.2
  have hw : (C.1.fst ≫ f) ≫ b = (C.1.snd ≫ g) ≫ b := by
    simpa only [Category.assoc] using hC.w
  let m := hQ.lift (C.1.fst ≫ f) (C.1.snd ≫ g) hw
  obtain ⟨D, e, he⟩ := compactQuasiEtaleDiagonalDomain hQ hU hb
  let E := domainPreimage m D
  have hE : IsPullback (domainPreimageMap m D ≫ e.inv) (domainι C.1.pt E)
      (hQ.lift (𝟙 U) (𝟙 U) rfl) m := by
    apply (domainPreimage_isPullback m D).flip.of_iso' (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simp
    · simp [E]
    · simpa only [Iso.refl_hom, Category.comp_id] using he.symm
    · simp
  have hP := isPullback_of_relative_diagonal hC hQ
    (hQ.lift_fst _ _ hw) (hQ.lift_snd _ _ hw) (hQ.lift_fst _ _ rfl) (hQ.lift_snd _ _ rfl) hE
  have hC' := (hasLocalDomainEtaleFactorizations_of_quasiEtale hf).of_isPullback_common
    (hasLocalDomainEtaleFactorizations_of_quasiEtale hg) hC
  let i := h.isoIsPullback _ _ hP
  have hi : i.hom ≫ (domainι C.1.pt E ≫ C.1.snd) = q :=
    h.isoIsPullback_hom_snd _ _ hP
  apply (hC'.domainι_comp E).of_iso i (Iso.refl X)
  simp only [← Category.assoc, hi, Iso.refl_hom, Category.comp_id]

/-- The relative pullback of two Hausdorff spaces quasi-étale over a common
base still maps quasi-étale to that base when the intermediate object is
Hausdorff and quasi-étale over it. -/
theorem quasiEtale_common_of_isPullback_over
    [T2Space (localizedSpaceFunctor.obj A)] [T2Space (localizedSpaceFunctor.obj B)]
    [T2Space (localizedSpaceFunctor.obj U)]
    {f : A ⟶ U} {g : B ⟶ U} {b : U ⟶ X} {p : P ⟶ A} {q : P ⟶ B}
    (h : IsPullback p q f g) (hb : quasiEtale b)
    (hf : quasiEtale (f ≫ b)) (hg : quasiEtale (g ≫ b)) :
    quasiEtale (q ≫ g ≫ b) := by
  apply HasLocalDomainEtaleFactorizations.quasiEtale
  apply HasLocalDomainEtaleFactorizations.of_domain_cover
  intro x
  obtain ⟨D, hD, hDx⟩ := exists_compact_domain_nhds U (localizedSpaceFunctor.map (q ≫ g) x)
  let S := domainPreimage f D
  let T := domainPreimage g D
  let E := domainPreimage p S ⊓ domainPreimage q T
  have hE : E.carrier = localizedSpaceFunctor.map (q ≫ g) ⁻¹' D.carrier := by
    ext y
    change localizedSpaceFunctor.obj P at y
    change (localizedSpaceFunctor.map f (localizedSpaceFunctor.map p y) ∈ D.carrier ∧
      localizedSpaceFunctor.map g (localizedSpaceFunctor.map q y) ∈ D.carrier) ↔
      localizedSpaceFunctor.map (q ≫ g) y ∈ D.carrier
    have hw := congrArg (fun k : P ⟶ U => localizedSpaceFunctor.map k y) h.w
    have hp : localizedSpaceFunctor.map (p ≫ f) y =
        localizedSpaceFunctor.map f (localizedSpaceFunctor.map p y) := by
      rw [Functor.map_comp]
      rfl
    have hq : localizedSpaceFunctor.map (q ≫ g) y =
        localizedSpaceFunctor.map g (localizedSpaceFunctor.map q y) := by
      rw [Functor.map_comp]
      rfl
    rw [← hp, ← hq, hw, and_self]
  have hn : E.carrier ∈ 𝓝 x := hE ▸
    (localizedSpaceFunctor.map (q ≫ g)).hom.continuous.continuousAt.preimage_mem_nhds hDx
  refine ⟨{E}, finite_singleton _, by simpa using hn, ?_⟩
  intro F hF
  obtain rfl : F = E := mem_singleton_iff.mp hF
  refine ⟨mem_of_mem_nhds hn, ?_⟩
  let a := domainPreimageMap f D
  let c := domainPreimageMap g D
  let r := domainOrderMap (inf_le_left : E ≤ domainPreimage p S) ≫ domainPreimageMap p S
  let s := domainOrderMap (inf_le_right : E ≤ domainPreimage q T) ≫ domainPreimageMap q T
  have h' : IsPullback r s (a ≫ domainι U D) (c ≫ domainι U D) := by
    simp only [a, c, domainPreimageMap_comp_inclusion]
    exact isPullback_domainPreimage_inf h S T
  have hpb : IsPullback r s a c := by
    apply IsPullback.mk'
    · apply (cancel_mono (domainι U D)).mp
      simpa only [Category.assoc] using h'.w
    · intro Z r' s' hr hs
      exact h'.hom_ext hr hs
    · intro Z r' s' hw
      have hw' : r' ≫ (a ≫ domainι U D) = s' ≫ (c ≫ domainι U D) := by
        rw [← Category.assoc, hw, Category.assoc]
      exact ⟨h'.lift r' s' hw', h'.lift_fst _ _ _, h'.lift_snd _ _ _⟩
  let : T2Space (presentationOf A).presentation.space :=
    inferInstanceAs (T2Space (localizedSpaceFunctor.obj A))
  let : T2Space (presentationOf B).presentation.space :=
    inferInstanceAs (T2Space (localizedSpaceFunctor.obj B))
  let : T2Space (localizedSpaceFunctor.obj (domainObj A S)) :=
    inferInstanceAs (T2Space S.carrier)
  let : T2Space (localizedSpaceFunctor.obj (domainObj B T)) :=
    inferInstanceAs (T2Space T.carrier)
  let j := domainι U D ≫ b
  have ha : a ≫ j = domainι A S ≫ f ≫ b := by
    rw [← Category.assoc, domainPreimageMap_comp_inclusion, Category.assoc]
  have hc : c ≫ j = domainι B T ≫ g ≫ b := by
    rw [← Category.assoc, domainPreimageMap_comp_inclusion, Category.assoc]
  have hs : s ≫ c ≫ j = domainι P E ≫ q ≫ g ≫ b := by
    rw [hc]
    simp only [s, Category.assoc, domainPreimageMap_comp_inclusion_assoc,
      domainOrderMap_comp_inclusion_assoc]
    rfl
  rw [← hs]
  exact common_of_pullback_over_compact hpb hD
    ((hasLocalDomainEtaleFactorizations_of_quasiEtale hb).domainι_comp D).quasiEtale
    (ha.symm ▸ ((hasLocalDomainEtaleFactorizations_of_quasiEtale hf).domainι_comp S).quasiEtale)
    (hc.symm ▸ ((hasLocalDomainEtaleFactorizations_of_quasiEtale hg).domainι_comp T).quasiEtale)

namespace EquivariantQuasiEtaleSite

variable {G : Type z} [Group G] [TopologicalSpace G]
  {X : GSpace.{u, v, v} K G}

/-- Every arrow of the equivariant quasi-étale site is quasi-étale on analytic spaces. -/
theorem quasiEtale_map_left {U V : EquivariantQuasiEtaleSite X} (f : U ⟶ V) :
    quasiEtale (GSpace.forget.map f.left) := by
  let : T2Space (localizedSpaceFunctor.obj (GSpace.forget.obj U.left)) := U.left.2.1
  let : T2Space (localizedSpaceFunctor.obj (GSpace.forget.obj V.left)) := V.left.2.1
  have hw : GSpace.forget.map f.left ≫ GSpace.forget.map V.hom = GSpace.forget.map U.hom := by
    rw [← GSpace.forget.map_comp, MorphismProperty.Over.w]
  exact quasiEtale_of_over_of_t2Space V.prop (hw.symm ▸ U.prop)

end EquivariantQuasiEtaleSite

/-- Every equivariant quasi-étale site cospan has a pullback in the underlying
analytic category, with its continuous diagonal group action. -/
theorem equivariantQuasiEtalePullbacks : EquivariantQuasiEtalePullbacksStatement.{u, v, z} := by
  intro K _ _ _ G _ _ X A B U f g
  let a := GSpace.forget.map f.left
  let b := GSpace.forget.map g.left
  let h := GSpace.forget.map U.hom
  have ha : quasiEtale a := EquivariantQuasiEtaleSite.quasiEtale_map_left f
  let : T2Space (localizedSpaceFunctor.obj (GSpace.forget.obj A.left)) := A.left.2.1
  let : T2Space (localizedSpaceFunctor.obj (GSpace.forget.obj B.left)) := B.left.2.1
  let : T2Space (localizedSpaceFunctor.obj (GSpace.forget.obj U.left)) := U.left.2.1
  obtain ⟨P, p, q, hp⟩ := exists_localizedPullback_of_quasiEtale a b ha
  have hf : a ≫ h = GSpace.forget.map A.hom := by
    rw [← GSpace.forget.map_comp, MorphismProperty.Over.w]
  have hg : b ≫ h = GSpace.forget.map B.hom := by
    rw [← GSpace.forget.map_comp, MorphismProperty.Over.w]
  exact exists_equivariantSitePullback_of_isPullback f g hp ha
    (hg ▸ quasiEtale_common_of_isPullback_over hp U.prop (hf.symm ▸ A.prop) (hg.symm ▸ B.prop))

end Langlands.Analytic.SaturatedAtlasPresentation
