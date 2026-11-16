import Langlands.Geometry.Analytic.FieldValuedPoints
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCompletedResidueStatement
import Langlands.Geometry.Analytic.Spectrum.ResidueField.CharacterTransport

/-! # Extending a chart character into a fixed complete field -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  {A : AffinoidAtlasPresentation.{u, v, w} K}

/-- The character has the norm of the specified point in this chart. -/
def IsChartCharacter (x : A.space) (i : A.atlas.Index)
    (g : A.atlas.algebra i →ₐ[K] L) : Prop :=
  ∃ y : BanachSpectrum (A.atlas.algebra i),
    A.atlas.chart i y = x ∧ ∀ a, ‖g a‖ = y a

omit [CompleteSpace L] in
theorem IsChartCharacter.comp_restriction {x : A.space} {i j : A.atlas.Index}
    {g : A.atlas.algebra i →ₐ[K] L} (hg : IsChartCharacter x i g)
    (hij : range (A.atlas.chart i) ⊆ range (A.atlas.chart j)) :
    IsChartCharacter x j (g.comp (A.atlas.restriction i j hij).toAlgHom) := by
  obtain ⟨y, hy, hn⟩ := hg
  exact ⟨BanachSpectrum.comap (A.atlas.restriction i j hij).toBoundedRingHom y,
    (A.atlas.restriction_chart i j hij y).trans hy, fun a => hn _⟩

/-- The domain residue comparison makes extension to a smaller containing
chart unique, for the same fixed target field. -/
theorem existsUnique_chartCharacter_lift
    (hd : DomainCompletedResidueSurjectivityStatement.{u}) (x : A.space)
    (i j : A.atlas.Index) (hij : range (A.atlas.chart i) ⊆ range (A.atlas.chart j))
    (hi : x ∈ range (A.atlas.chart i)) (g : A.atlas.algebra j →ₐ[K] L)
    (hg : IsChartCharacter x j g) :
    ∃! h : A.atlas.algebra i →ₐ[K] L,
      IsChartCharacter x i h ∧ h.comp (A.atlas.restriction i j hij).toAlgHom = g := by
  obtain ⟨y, hy⟩ := hi
  obtain ⟨z, hz, hn⟩ := hg
  have hyz : BanachSpectrum.comap (A.atlas.restriction i j hij).toBoundedRingHom y = z :=
    (A.atlas.isEmbedding_chart j).injective
      ((A.atlas.restriction_chart i j hij y).trans (hy.trans hz.symm))
  have hs := hd K (A.atlas.algebra j) (A.atlas.algebra i)
    (A.atlas.restriction i j hij) _ (A.atlas.restriction_represents i j hij) y
  obtain ⟨h, hh, -⟩ :=
    BanachSpectrum.existsUnique_character_lift_of_surjective_completedResidueComap K
      (A.atlas.restriction i j hij) y hs g (fun a => (hn a).trans (congrArg (fun p => p a) hyz.symm))
  refine ⟨h.toAlgHom, ⟨⟨y, hy, hh.1⟩, AlgHom.ext hh.2⟩, ?_⟩
  rintro h' ⟨⟨y', hy', hn'⟩, hr⟩
  have he : y' = y := (A.atlas.isEmbedding_chart i).injective (hy'.trans hy.symm)
  subst y'
  exact BanachSpectrum.character_eq_of_surjective_completedResidueComap K
    (A.atlas.restriction i j hij) y hs h' h.toAlgHom hn' hh.1
    (fun a => (AlgHom.congr_fun hr a).trans (hh.2 a).symm)

private def ChartExtension (x : A.space) (i₀ : A.atlas.Index)
    (g₀ : A.atlas.algebra i₀ →ₐ[K] L) (j : A.atlas.Index)
    (g : A.atlas.algebra j →ₐ[K] L) : Prop :=
  IsChartCharacter x j g ∧
    ∃ (m : A.atlas.Index)
      (hm₀ : range (A.atlas.chart m) ⊆ range (A.atlas.chart i₀))
      (hmj : range (A.atlas.chart m) ⊆ range (A.atlas.chart j)),
      x ∈ range (A.atlas.chart m) ∧
      ∃ c : A.atlas.algebra m →ₐ[K] L, IsChartCharacter x m c ∧
        c.comp (A.atlas.restriction m i₀ hm₀).toAlgHom = g₀ ∧
        c.comp (A.atlas.restriction m j hmj).toAlgHom = g

omit [CompleteSpace L] in
private theorem chartExtension_comp {x : A.space} {i₀ i j : A.atlas.Index}
    {g₀ : A.atlas.algebra i₀ →ₐ[K] L} {g : A.atlas.algebra i →ₐ[K] L}
    (hg : ChartExtension x i₀ g₀ i g)
    (hij : range (A.atlas.chart i) ⊆ range (A.atlas.chart j)) :
    ChartExtension x i₀ g₀ j (g.comp (A.atlas.restriction i j hij).toAlgHom) := by
  obtain ⟨hg, m, hm₀, hmi, hm, c, hc, hc₀, hci⟩ := hg
  refine ⟨hg.comp_restriction hij, m, hm₀, hmi.trans hij, hm, c, hc, hc₀, ?_⟩
  rw [A.atlas.restriction_comp m i j hmi hij (hmi.trans hij)]
  rw [← hci]
  rfl

private theorem chartExtension_unique
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    {x : A.space} {i₀ j : A.atlas.Index} {g₀ : A.atlas.algebra i₀ →ₐ[K] L}
    {g g' : A.atlas.algebra j →ₐ[K] L}
    (hg₀ : IsChartCharacter x i₀ g₀)
    (hg : ChartExtension x i₀ g₀ j g) (hg' : ChartExtension x i₀ g₀ j g') : g = g' := by
  obtain ⟨-, m, hm₀, hmj, hm, c, hc, hc₀, hcj⟩ := hg
  obtain ⟨-, n, hn₀, hnj, hn, d, hd', hd₀, hdj⟩ := hg'
  obtain ⟨r, hr, hxr⟩ := IndexedAffinoidAtlas.exists_chart_inter hm hn
  have hrm := hr.trans inter_subset_left
  have hrn := hr.trans inter_subset_right
  obtain ⟨e, he, -⟩ := existsUnique_chartCharacter_lift hd x r m hrm hxr c hc
  obtain ⟨f, hf, -⟩ := existsUnique_chartCharacter_lift hd x r n hrn hxr d hd'
  have he₀ : e.comp (A.atlas.restriction r i₀ (hrm.trans hm₀)).toAlgHom = g₀ := by
    rw [A.atlas.restriction_comp r m i₀ hrm hm₀ (hrm.trans hm₀)]
    change (e.comp (A.atlas.restriction r m hrm).toAlgHom).comp
      (A.atlas.restriction m i₀ hm₀).toAlgHom = g₀
    rw [he.2, hc₀]
  have hf₀ : f.comp (A.atlas.restriction r i₀ (hrm.trans hm₀)).toAlgHom = g₀ := by
    rw [A.atlas.restriction_comp r n i₀ hrn hn₀ (hrm.trans hm₀)]
    change (f.comp (A.atlas.restriction r n hrn).toAlgHom).comp
      (A.atlas.restriction n i₀ hn₀).toAlgHom = g₀
    rw [hf.2, hd₀]
  have hef : e = f :=
    (existsUnique_chartCharacter_lift hd x r i₀ (hrm.trans hm₀) hxr g₀ hg₀).unique
      ⟨he.1, he₀⟩ ⟨hf.1, hf₀⟩
  have hej : e.comp (A.atlas.restriction r j (hrm.trans hmj)).toAlgHom = g := by
    rw [A.atlas.restriction_comp r m j hrm hmj (hrm.trans hmj)]
    change (e.comp (A.atlas.restriction r m hrm).toAlgHom).comp
      (A.atlas.restriction m j hmj).toAlgHom = g
    rw [he.2, hcj]
  have hfj : f.comp (A.atlas.restriction r j (hrm.trans hmj)).toAlgHom = g' := by
    rw [A.atlas.restriction_comp r n j hrn hnj (hrm.trans hmj)]
    change (f.comp (A.atlas.restriction r n hrn).toAlgHom).comp
      (A.atlas.restriction n j hnj).toAlgHom = g'
    rw [hf.2, hdj]
  exact hej.symm.trans ((congrArg
    (fun a => a.comp (A.atlas.restriction r j (hrm.trans hmj)).toAlgHom) hef).trans hfj)

private theorem existsUnique_chartExtension
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    {x : A.space} {i₀ : A.atlas.Index} {g₀ : A.atlas.algebra i₀ →ₐ[K] L}
    (h₀ : x ∈ range (A.atlas.chart i₀)) (hg₀ : IsChartCharacter x i₀ g₀)
    (j : A.atlas.Index) (hj : x ∈ range (A.atlas.chart j)) :
    ∃! g : A.atlas.algebra j →ₐ[K] L, ChartExtension x i₀ g₀ j g := by
  obtain ⟨m, hm, hxm⟩ := IndexedAffinoidAtlas.exists_chart_inter h₀ hj
  have hm₀ := hm.trans inter_subset_left
  have hmj := hm.trans inter_subset_right
  obtain ⟨c, hc, -⟩ := existsUnique_chartCharacter_lift hd x m i₀ hm₀ hxm g₀ hg₀
  refine ⟨c.comp (A.atlas.restriction m j hmj).toAlgHom,
    ⟨hc.1.comp_restriction hmj, m, hm₀, hmj, hxm, c, hc.1, hc.2, rfl⟩, ?_⟩
  intro g hg
  exact chartExtension_unique hd hg₀ hg
    ⟨hc.1.comp_restriction hmj, m, hm₀, hmj, hxm, c, hc.1, hc.2, rfl⟩

namespace FieldPoint

/-- Two field-valued points with equal underlying point and equal evaluation
in one containing chart are equal, assuming domain residue comparison. -/
theorem eq_of_eval_eq (hd : DomainCompletedResidueSurjectivityStatement.{u})
    {p q : FieldPoint L A} (hpq : p.point = q.point)
    (i₀ : A.atlas.Index) (hp₀ : p.point ∈ range (A.atlas.chart i₀))
    (hq₀ : q.point ∈ range (A.atlas.chart i₀)) (he₀ : p.eval i₀ hp₀ = q.eval i₀ hq₀) :
    p = q := by
  refine ext' hpq fun j hpj hqj => ?_
  have hp : ChartExtension p.point i₀ (p.eval i₀ hp₀) j (p.eval j hpj) := by
    obtain ⟨m, hm, hxm⟩ := IndexedAffinoidAtlas.exists_chart_inter hp₀ hpj
    exact ⟨p.isChartPoint j hpj, m, hm.trans inter_subset_left, hm.trans inter_subset_right,
      hxm, p.eval m hxm, p.isChartPoint m hxm,
      p.eval_restriction m i₀ _ hxm, p.eval_restriction m j _ hxm⟩
  have hq : ChartExtension q.point i₀ (q.eval i₀ hq₀) j (q.eval j hqj) := by
    obtain ⟨m, hm, hxm⟩ := IndexedAffinoidAtlas.exists_chart_inter hq₀ hqj
    exact ⟨q.isChartPoint j hqj, m, hm.trans inter_subset_left, hm.trans inter_subset_right,
      hxm, q.eval m hxm, q.isChartPoint m hxm,
      q.eval_restriction m i₀ _ hxm, q.eval_restriction m j _ hxm⟩
  rw [← hpq, ← he₀] at hq
  exact chartExtension_unique hd (p.isChartPoint i₀ hp₀) hp hq

/-- A prescribed point-realizing chart character extends uniquely to a
field-valued point in the same complete target field. -/
theorem existsUnique_of_chartCharacter
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (x : A.space) (i₀ : A.atlas.Index) (g₀ : A.atlas.algebra i₀ →ₐ[K] L)
    (hg₀ : IsChartCharacter x i₀ g₀) :
    ∃! p : FieldPoint L A,
      p.point = x ∧ ∃ h₀ : p.point ∈ range (A.atlas.chart i₀), p.eval i₀ h₀ = g₀ := by
  classical
  have h₀ : x ∈ range (A.atlas.chart i₀) := by
    obtain ⟨y, hy, -⟩ := hg₀
    exact ⟨y, hy⟩
  let e := fun j (hj : x ∈ range (A.atlas.chart j)) =>
    (existsUnique_chartExtension hd h₀ hg₀ j hj).choose
  have he (j) (hj : x ∈ range (A.atlas.chart j)) :
      ChartExtension x i₀ g₀ j (e j hj) :=
    (existsUnique_chartExtension hd h₀ hg₀ j hj).choose_spec.1
  let p : FieldPoint L A := {
    point := x
    eval := e
    isChartPoint := fun j hj => (he j hj).1
    eval_restriction := fun i j hij hi =>
      chartExtension_unique hd hg₀ (chartExtension_comp (he i hi) hij) (he j (hij hi))
  }
  have he₀ : p.eval i₀ h₀ = g₀ := by
    apply chartExtension_unique hd hg₀ (he i₀ h₀)
    refine ⟨hg₀, i₀, subset_rfl, subset_rfl, h₀, g₀, hg₀, ?_, ?_⟩ <;>
      rw [A.atlas.restriction_id] <;> rfl
  refine ⟨p, ⟨rfl, h₀, he₀⟩, ?_⟩
  rintro q ⟨hq, hq₀, heq⟩
  exact eq_of_eval_eq hd hq i₀ hq₀ h₀ (heq.trans he₀.symm)

end FieldPoint

end Langlands.Analytic.AffinoidAtlasPresentation
