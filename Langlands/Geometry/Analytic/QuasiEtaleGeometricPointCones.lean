import Langlands.Geometry.Analytic.CompactQuasiEtaleDiagonal
import Langlands.Geometry.Analytic.QuasiEtaleCommonProduct
import Langlands.Geometry.Analytic.QuasiEtaleFieldPointPullback

/-! # Pointed common refinements and equalization in the quasi-étale site -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleSite

open _root_.CategoryTheory Limits Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [IsAlgClosed L] [NormedAlgebra K L]

local notation "Φ" => localizedFieldPointFunctor (K := K) L

set_option backward.isDefEq.respectTransparency false in
omit [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L] in
private theorem exists_pointed_domainEtale_chart
    {A X : LocalizedCategory.{u, v, v} (K := K)} {f : A ⟶ X}
    (hf : quasiEtale f) (p : (Φ).obj A) :
    ∃ (C : LocalizedCategory.{u, v, v} (K := K)) (c : C ⟶ A) (q : (Φ).obj C),
      IsCompactSpace C ∧ IsAnalyticDomainEmbedding c ∧
        HasDomainEtaleFactorization (c ≫ f) ∧ (Φ).map c q = p := by
  obtain ⟨A₀, X₀, g, hg, ⟨e⟩⟩ := hf
  let a : localizationFunctor.obj (ofSaturation A₀) ≅ A := Arrow.leftFunc.mapIso e
  let b : localizationFunctor.obj (ofSaturation X₀) ≅ X := Arrow.rightFunc.mapIso e
  let p₀ := (Φ).map a.inv p
  obtain ⟨σ, _, hn, hσ⟩ := hg.exists_local_domainEtale_charts
    (((localizedFieldPointProjection L).app _ p₀).down)
  obtain ⟨V, hV, hx⟩ := Set.mem_sUnion.mp (mem_of_mem_nhds hn)
  obtain ⟨i, hi, hf₀⟩ := hσ V hV
  let D := (ofSaturation A₀).chartDomain i
  have hxD : ((localizedFieldPointProjection L).app _ p₀).down ∈ D.carrier := by
    change _ ∈ ((ofSaturation A₀).chartDomain i).carrier
    rwa [chartDomain_carrier, hi]
  obtain ⟨q, hq⟩ := exists_fieldPoint_lift_domainι D p₀ hxD
  let ι := domainι (localizationFunctor.obj (ofSaturation A₀)) D
  have hab : a.hom ≫ f = localizationFunctor.map g ≫ b.hom := e.hom.w
  have hfac : HasDomainEtaleFactorization ((ι ≫ a.hom) ≫ f) := by
    rw [Category.assoc, hab, ← Category.assoc]
    exact hf₀.comp_iso b
  refine ⟨_, ι ≫ a.hom, q, isCompactSpace_chartDomainObj (ofSaturation A₀) i, ?_, hfac, ?_⟩
  · refine ⟨domainPreimage a.inv D, domainImageIso a D, ?_⟩
    exact (domainImageIso_hom_inclusion a D).symm
  · rw [Functor.map_comp_apply, hq]
    exact Iso.inv_hom_id_apply ((Φ).mapIso a) p

set_option backward.isDefEq.respectTransparency false in
omit [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L] in
private theorem exists_pointed_domainEtale_site_chart
    {X : LocalizedCategory.{u, v, v} (K := K)} (U : QuasiEtaleSite X) (p : (Φ).obj U.left) :
    ∃ (C : QuasiEtaleSite X) (c : C ⟶ U) (q : (Φ).obj C.left),
      IsCompactSpace C.left ∧ IsAnalyticDomainEmbedding c.left ∧
        HasDomainEtaleFactorization C.hom ∧ (Φ).map c.left q = p := by
  obtain ⟨A, a, q, hc, ha, hA, hq⟩ := exists_pointed_domainEtale_chart U.prop p
  let C : QuasiEtaleSite X := MorphismProperty.Over.mk ⊤ (a ≫ U.hom) hA.quasiEtale
  exact ⟨C, MorphismProperty.Over.homMk a, q, hc, ha, hA, hq⟩

set_option backward.isDefEq.respectTransparency false in
/-- A common refinement may be taken to be the product of two domains admitting étale envelopes. -/
theorem geometricPointRefinement : GeometricPointRefinementStatement.{u, v, uL} := by
  intro K _ _ _ L _ _ _ _ _ X U V p q hpq
  let F := localizedFieldPointFunctor (K := K) L
  obtain ⟨A, a, p', _, _, hA, hp⟩ := exists_pointed_domainEtale_site_chart U p
  obtain ⟨B, b, q', _, _, hB, hq⟩ := exists_pointed_domainEtale_site_chart V q
  obtain ⟨P, s, t, h⟩ := exists_localizedPullback_of_quasiEtale A.hom B.hom A.prop
  have hP := hA.of_isPullback_common hB h
  let W : QuasiEtaleSite X := MorphismProperty.Over.mk ⊤ (t ≫ B.hom) hP.quasiEtale
  let s' : W ⟶ A := MorphismProperty.Over.homMk s h.w
  let t' : W ⟶ B := MorphismProperty.Over.homMk t
  change F.map a.left p' = p at hp
  change F.map b.left q' = q at hq
  have hpa : F.map A.hom p' = F.map U.hom p := calc
    _ = F.map (a.left ≫ U.hom) p' := congrArg (fun k => F.map k p') (MorphismProperty.Over.w a).symm
    _ = F.map U.hom (F.map a.left p') := F.map_comp_apply _ _ _
    _ = _ := congrArg (fun x => F.map U.hom x) hp
  have hqb : F.map B.hom q' = F.map V.hom q := calc
    _ = F.map (b.left ≫ V.hom) q' := congrArg (fun k => F.map k q') (MorphismProperty.Over.w b).symm
    _ = F.map V.hom (F.map b.left q') := F.map_comp_apply _ _ _
    _ = _ := congrArg (fun x => F.map V.hom x) hq
  have he : F.map A.hom p' = F.map B.hom q' := hpa.trans (hpq.trans hqb.symm)
  obtain ⟨r, hs, ht⟩ := Types.exists_of_isPullback
    (localizedQuasiEtaleFieldPointPullback _ _ _ _ A.prop h) p' q' he
  refine ⟨W, s' ≫ a, t' ≫ b, r, ?_, ?_⟩
  · change F.map (s ≫ a.left) r = p
    exact (F.map_comp_apply _ _ _).trans ((congrArg (fun x => F.map a.left x) hs).trans hp)
  · change F.map (t ≫ b.left) r = q
    exact (F.map_comp_apply _ _ _).trans ((congrArg (fun x => F.map b.left x) ht).trans hq)

set_option backward.isDefEq.respectTransparency false in
omit [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L] in
private theorem fieldPoint_factors_domainEmbedding
    {T B V : LocalizedCategory.{u, v, v} (K := K)} (b : B ⟶ V)
    (D : (presentationOf V).AnalyticDomain) (e : B ≅ domainObj V D)
    (hb : b = e.hom ≫ domainι V D) (r s : T ⟶ V)
    (p : (Φ).obj T) (q : (Φ).obj B) (hr : (Φ).map r p = (Φ).map b q)
    (hs : (Φ).map s p = (Φ).map b q) :
    ∃ (E : (presentationOf T).AnalyticDomain) (p' : (Φ).obj (domainObj T E))
      (r' s' : domainObj T E ⟶ B),
      (Φ).map (domainι T E) p' = p ∧ r' ≫ b = domainι T E ≫ r ∧
      s' ≫ b = domainι T E ≫ s ∧ (Φ).map r' p' = q ∧ (Φ).map s' p' = q := by
  let E := domainPreimage r D ⊓ domainPreimage s D
  let j := domainι T E
  have hm (f : T ⟶ V) (hf : (Φ).map f p = (Φ).map b q) :
      ((localizedFieldPointProjection L).app T p).down ∈ (domainPreimage f D).carrier := by
    change localizedSpaceFunctor.map f _ ∈ D.carrier
    rw [← localizedFieldPointProjection_map_down f, hf, hb,
      localizedFieldPointProjection_map_down, Functor.map_comp, TopCat.comp_app, domainι_apply]
    exact (localizedSpaceFunctor.map e.hom (((localizedFieldPointProjection L).app B q).down)).property
  obtain ⟨p', hp'⟩ := exists_fieldPoint_lift_domainι E p ⟨hm r hr, hm s hs⟩
  let toB (f : T ⟶ V) (hf : E ≤ domainPreimage f D) : domainObj T E ⟶ B :=
    domainOrderMap hf ≫ domainPreimageMap f D ≫ e.inv
  have hw (f : T ⟶ V) (hf : E ≤ domainPreimage f D) : toB f hf ≫ b = j ≫ f := by
    rw [hb]
    simp only [toB, j, Category.assoc, Iso.inv_hom_id_assoc,
      domainPreimageMap_comp_inclusion, domainOrderMap_comp_inclusion_assoc]
  have hi : Function.Injective (((Φ).map b) : (Φ).obj B → (Φ).obj V) := by
    rw [hb, Functor.map_comp]
    exact (localizedFieldPoint_map_domainι_injective (L := L) D).comp
      ((isIso_iff_bijective ((Φ).map e.hom)).mp inferInstance).1
  have hl (f : T ⟶ V) (hf : E ≤ domainPreimage f D)
      (h : (Φ).map f p = (Φ).map b q) : (Φ).map (toB f hf) p' = q := by
    apply hi
    rw [← Functor.map_comp_apply, hw, Functor.map_comp_apply, hp', h]
  exact ⟨E, p', toB r inf_le_left, toB s inf_le_right, hp', hw r inf_le_left,
    hw s inf_le_right, hl r inf_le_left hr, hl s inf_le_right hs⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_domain_equalizing_at_point
    {T B X : LocalizedCategory.{u, v, v} (K := K)} {b : B ⟶ X}
    (hb : quasiEtale b) (hc : IsCompactSpace B) (r s : T ⟶ B) (h : r ≫ b = s ≫ b)
    (p : (Φ).obj T) (q : (Φ).obj B) (hr : (Φ).map r p = q) (hs : (Φ).map s p = q) :
    ∃ (D : (presentationOf T).AnalyticDomain) (p' : (Φ).obj (domainObj T D)),
      (Φ).map (domainι T D) p' = p ∧ domainι T D ≫ r = domainι T D ≫ s := by
  obtain ⟨P, u, v, hP⟩ := exists_localizedPullback_of_quasiEtale b b hb
  let d := hP.lift (𝟙 B) (𝟙 B) rfl
  have hd₁ : d ≫ u = 𝟙 _ := hP.lift_fst _ _ _
  have hd₂ : d ≫ v = 𝟙 _ := hP.lift_snd _ _ _
  obtain ⟨E, e, hd⟩ := compactQuasiEtaleDiagonalDomain hP hc hb
  let t := hP.lift r s h
  have ht₁ : t ≫ u = r := hP.lift_fst _ _ _
  have ht₂ : t ≫ v = s := hP.lift_snd _ _ _
  have hEq : (Φ).map t p = (Φ).map d q := by
    apply Types.ext_of_isPullback (localizedQuasiEtaleFieldPointPullback _ _ _ _ hb hP)
    · rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ht₁, hd₁, (Φ).map_id_apply, hr]
    · rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ht₂, hd₂, (Φ).map_id_apply, hs]
  obtain ⟨D, p', l, _, hp, hl, _, _, _⟩ := fieldPoint_factors_domainEmbedding d E e hd t t p q hEq hEq
  refine ⟨D, p', hp, ?_⟩
  rw [← ht₁, ← ht₂, ← Category.assoc, ← Category.assoc, ← hl, Category.assoc, Category.assoc,
    hd₁, hd₂]

set_option backward.isDefEq.respectTransparency false in
/-- Parallel site arrows agreeing at a full field point have a pointed equalizing refinement. -/
theorem geometricPointEqualization : GeometricPointEqualizationStatement.{u, v, uL} := by
  intro K _ _ _ L _ _ _ _ _ X U V f g p hfg
  let F := localizedFieldPointFunctor (K := K) L
  obtain ⟨A, a, p', _, _, hA, hp⟩ := exists_pointed_domainEtale_site_chart U p
  obtain ⟨B, b, q, hB, hb, _, hq⟩ := exists_pointed_domainEtale_site_chart V (F.map f.left p)
  obtain ⟨D, e, hbD⟩ := hb
  let r := a.left ≫ f.left
  let s := a.left ≫ g.left
  have hr : F.map r p' = F.map b.left q := by rw [Functor.map_comp_apply, hp, hq]
  have hs : F.map s p' = F.map b.left q := by rw [Functor.map_comp_apply, hp, ← hfg, hq]
  obtain ⟨E, p'', r', s', hp'', hr', hs', hpr, hps⟩ :=
    fieldPoint_factors_domainEmbedding b.left D e hbD r s p' q hr hs
  let j := domainι A.left E
  have has (z : A.left ⟶ V.left) (z' : domainObj A.left E ⟶ B.left)
      (h : z' ≫ b.left = j ≫ z) (hz : z ≫ V.hom = A.hom) : z' ≫ B.hom = j ≫ A.hom := by
    rw [← MorphismProperty.Over.w b, ← Category.assoc, h, Category.assoc, hz]
  have hcomp : r' ≫ B.hom = s' ≫ B.hom :=
    (has r r' hr' (by simp only [r, Category.assoc, MorphismProperty.Over.w])).trans
      (has s s' hs' (by simp only [s, Category.assoc, MorphismProperty.Over.w])).symm
  obtain ⟨G, p''', hp''', hk⟩ := exists_domain_equalizing_at_point B.prop hB r' s' hcomp p'' q hpr hps
  let k := domainι (domainObj A.left E) G
  have hfac := (hA.domainι_comp E).domainι_comp G
  let W : QuasiEtaleSite X := MorphismProperty.Over.mk ⊤ (k ≫ j ≫ A.hom) hfac.quasiEtale
  let l : W ⟶ A := MorphismProperty.Over.homMk (k ≫ j) (by simp [W, Category.assoc])
  refine ⟨W, l ≫ a, p''', ?_, ?_⟩
  · apply MorphismProperty.Over.Hom.ext
    change ((k ≫ j) ≫ a.left) ≫ f.left = ((k ≫ j) ≫ a.left) ≫ g.left
    have hh := congrArg (· ≫ b.left) hk
    rw [Category.assoc, Category.assoc, hr', hs'] at hh
    simpa only [Category.assoc, r, s] using hh
  · change (localizedFieldPointFunctor L).map ((k ≫ j) ≫ a.left) p''' = p
    rw [Functor.map_comp_apply, Functor.map_comp_apply, hp''', hp'', hp]

end Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleSite
