import Langlands.Geometry.Analytic.FiniteMorphismSmallNeighborhoods
import Langlands.Geometry.Analytic.AffinoidPointwiseEtale
import Mathlib.RingTheory.Flat.Localization

/-! # Restrictions to clopen pieces are localizations at idempotents -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidAlgebra

variable {B : PresentedAffinoidAlgebra K}

/-- An idempotent taking the value `1` at every point is `1`. -/
theorem idempotent_eq_one_of_forall {e : B} (he : IsIdempotentElem e)
    (h1 : ∀ x : BanachSpectrum B, x e = 1) : e = 1 :=
  IsClopenIdempotent.unique (C := Set.univ) ⟨he, fun x _ => h1 x, fun _ hx => absurd trivial hx⟩
    ⟨IsIdempotentElem.one, fun x _ => map_one x.toMulRingSeminorm,
      fun _ hx => absurd trivial hx⟩

/-- An idempotent vanishing at every point is `0`. -/
theorem idempotent_eq_zero_of_forall {e : B} (he : IsIdempotentElem e)
    (h0 : ∀ x : BanachSpectrum B, x e = 0) : e = 0 :=
  IsClopenIdempotent.unique (C := ∅) ⟨he, fun _ hx => hx.elim, fun x _ => h0 x⟩
    ⟨IsIdempotentElem.zero, fun _ hx => hx.elim, fun x _ => map_zero x.toMulRingSeminorm⟩

variable (C : Set (BanachSpectrum B)) (hC : IsClopen C)

/-- A point of the chart algebra pulls back into the clopen set. -/
theorem comap_mem_of_clopenRationalChart (z : BanachSpectrum (clopenRationalChart C hC).algebra) :
    BanachSpectrum.comap (clopenRationalChart C hC).baseMap.toBoundedRingHom z ∈ C := by
  have h := (clopenRationalChart C hC).toDomain.represents.hasImageIn z
  change _ ∈ (clopenRationalChart C hC).locus at h
  rwa [locus_clopenRationalChart] at h

/-- The idempotent of a clopen set becomes `1` on its Weierstrass chart. -/
theorem baseMap_clopenIdempotent :
    (clopenRationalChart C hC).baseMap (clopenIdempotent C hC) = 1 := by
  obtain ⟨he, h1, -⟩ := isClopenIdempotent_clopenIdempotent C hC
  refine idempotent_eq_one_of_forall (he.map (clopenRationalChart C hC).baseMap.toAlgHom)
    fun z => ?_
  exact h1 _ (comap_mem_of_clopenRationalChart C hC z)

/-- The idempotent of a clopen set becomes `0` on the Weierstrass chart of the
complement. -/
theorem baseMap_compl_clopenIdempotent :
    (clopenRationalChart Cᶜ hC.compl).baseMap (clopenIdempotent C hC) = 0 := by
  obtain ⟨he, -, h0⟩ := isClopenIdempotent_clopenIdempotent C hC
  refine idempotent_eq_zero_of_forall (he.map (clopenRationalChart Cᶜ hC.compl).baseMap.toAlgHom)
    fun z => ?_
  exact h0 _ (comap_mem_of_clopenRationalChart Cᶜ hC.compl z)

/-- Two-member cover of the whole spectrum by the Weierstrass charts of a
clopen set and of its complement. -/
def clopenCover : Domain.FiniteCover (Domain.whole K B) where
  size := 2
  obj := ![(clopenRationalChart C hC).toDomain, (clopenRationalChart Cᶜ hC.compl).toDomain]
  map _ := Domain.inclusionOfSubset _ _ (Set.subset_univ _)
  covers x _ := by
    by_cases hx : x ∈ C
    · exact ⟨0, show x ∈ (clopenRationalChart C hC).locus by
        rw [locus_clopenRationalChart]; exact hx⟩
    · exact ⟨1, show x ∈ (clopenRationalChart Cᶜ hC.compl).locus by
        rw [locus_clopenRationalChart]; exact hx⟩

/-- An element killed by the chart of a clopen set is killed by its idempotent. -/
theorem clopenIdempotent_mul_eq_zero {a : B}
    (ha : (clopenRationalChart C hC).baseMap a = 0) : clopenIdempotent C hC * a = 0 := by
  let c := clopenCover C hC
  refine c.algebra_ext_of_restrict_eq fun i => ?_
  have hres : (c.map i).restriction = (c.obj i).baseMap := Domain.restriction_toWhole (c.map i)
  have key : (c.obj i).baseMap (clopenIdempotent C hC * a) = 0 := by
    rw [map_mul]
    fin_cases i
    · change (clopenRationalChart C hC).baseMap (clopenIdempotent C hC) *
        (clopenRationalChart C hC).baseMap a = 0
      rw [ha, mul_zero]
    · change (clopenRationalChart Cᶜ hC.compl).baseMap (clopenIdempotent C hC) *
        (clopenRationalChart Cᶜ hC.compl).baseMap a = 0
      rw [baseMap_compl_clopenIdempotent, zero_mul]
  exact (congrArg (fun φ : BoundedAlgHom K (Domain.whole K B).algebra (c.obj i).algebra =>
    φ (clopenIdempotent C hC * a)) hres).trans
      (key.trans (map_zero (c.map i).restriction.toAlgHom).symm)

/-- The Weierstrass chart of a clopen set is the localization away from its
idempotent. -/
theorem isLocalization_clopenRationalChart :
    letI := (clopenRationalChart C hC).baseMap.toAlgHom.toRingHom.toAlgebra
    IsLocalization.Away (clopenIdempotent C hC) (clopenRationalChart C hC).algebra := by
  let := (clopenRationalChart C hC).baseMap.toAlgHom.toRingHom.toAlgebra
  obtain ⟨M, -, hlift⟩ := exists_lift_clopenRationalChart C hC
  refine (_root_.isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {a b} hab => ?_⟩
  · rintro ⟨_, n, rfl⟩
    change IsUnit ((clopenRationalChart C hC).baseMap (clopenIdempotent C hC ^ n))
    rw [map_pow, baseMap_clopenIdempotent, one_pow]
    exact isUnit_one
  · obtain ⟨c, hc, -⟩ := hlift z
    refine ⟨(c, 1), ?_⟩
    change z * (clopenRationalChart C hC).baseMap 1 = (clopenRationalChart C hC).baseMap c
    rw [map_one, mul_one, hc]
  · refine ⟨⟨clopenIdempotent C hC, 1, pow_one _⟩, ?_⟩
    change clopenIdempotent C hC * a = clopenIdempotent C hC * b
    have hab' : (clopenRationalChart C hC).baseMap (a - b) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 hab
    have := clopenIdempotent_mul_eq_zero C hC hab'
    rw [mul_sub] at this
    exact sub_eq_zero.1 this

/-- The Weierstrass chart of a clopen set is a flat map. -/
theorem flat_clopenRationalChart :
    (clopenRationalChart C hC).baseMap.toAlgHom.toRingHom.Flat := by
  let := (clopenRationalChart C hC).baseMap.toAlgHom.toRingHom.toAlgebra
  have := isLocalization_clopenRationalChart C hC
  exact IsLocalization.flat _ (Submonoid.powers (clopenIdempotent C hC))

end PresentedAffinoidAlgebra

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

namespace RecognizedSubset

variable (Q P : a.saturatedAtlas.RecognizedSubset)

/-- If `Q ⊆ P` is cut out of `P` by an open set, its locus pulls back to a
clopen subset of the spectrum of `P`: the preimage is open, and compact as the
chart image of the compact locus of `Q`. -/
theorem isClopen_chart_preimage_of_eq_inter {O : Set X} (hO : IsOpen O)
    (hQ : Q.locus = P.locus ∩ O) : IsClopen (P.chart ⁻¹' Q.locus) := by
  have hQc : IsCompact Q.locus := isCompact_iff_compactSpace.2 inferInstance
  have himg : P.chart '' (P.chart ⁻¹' Q.locus) = Q.locus := by
    rw [Set.image_preimage_eq_inter_range, P.range_chart, hQ, Set.inter_comm,
      ← Set.inter_assoc, Set.inter_self]
  refine ⟨?_, ?_⟩
  · have : IsCompact (P.chart ⁻¹' Q.locus) := by
      rw [P.isEmbedding_chart.isCompact_iff, himg]
      exact hQc
    exact this.isClosed
  · have heq : P.chart ⁻¹' Q.locus = P.chart ⁻¹' O := by
      rw [hQ, Set.preimage_inter]
      have huniv : P.chart ⁻¹' P.locus = Set.univ := by
        rw [← P.range_chart]
        exact Set.preimage_range _
      rw [huniv, Set.univ_inter]
    rw [heq]
    exact hO.preimage P.chart.continuous

/-- The restriction to a recognized subset whose locus pulls back to a clopen
subset of the spectrum is the Weierstrass chart of that subset followed by a
bijective bounded map. Hence it is flat and surjective. -/
theorem restriction_flat_and_surjective (h : Q.locus ⊆ P.locus)
    (hC : IsClopen (P.chart ⁻¹' Q.locus)) :
    (Q.restriction P h).toAlgHom.toRingHom.Flat ∧ Function.Surjective (Q.restriction P h) := by
  let d := clopenRationalChart (P.chart ⁻¹' Q.locus) hC
  have h₁ : Represents K d.baseMap (P.chart ⁻¹' Q.locus) := by
    have h0 : Represents K d.baseMap d.locus := d.toDomain.represents
    rwa [locus_clopenRationalChart] at h0
  have h₂ := Q.restriction_represents P h
  obtain ⟨ψ₁, hψ₁, -⟩ := h₁.2.2 _ (Q.restriction P h) h₂.hasImageIn
  obtain ⟨ψ₂, hψ₂, -⟩ := h₂.2.2 _ d.baseMap h₁.hasImageIn
  have hid₁ : ψ₁.comp ψ₂ = BoundedAlgHom.id K Q.algebra :=
    (h₂.2.2 _ (Q.restriction P h) h₂.hasImageIn).unique
      (by rw [BoundedAlgHom.comp_assoc, hψ₂, hψ₁]) (BoundedAlgHom.id_comp _)
  have hid₂ : ψ₂.comp ψ₁ = BoundedAlgHom.id K d.algebra :=
    (h₁.2.2 _ d.baseMap h₁.hasImageIn).unique
      (by rw [BoundedAlgHom.comp_assoc, hψ₁, hψ₂]) (BoundedAlgHom.id_comp _)
  have hbij : Function.Bijective ψ₁ := by
    refine ⟨Function.LeftInverse.injective (g := ψ₂) fun z => ?_,
      Function.RightInverse.surjective (g := ψ₂) fun z => ?_⟩
    · exact congrArg (fun φ : BoundedAlgHom K d.algebra d.algebra => φ z) hid₂
    · exact congrArg (fun φ : BoundedAlgHom K Q.algebra Q.algebra => φ z) hid₁
  have hfac : (Q.restriction P h).toAlgHom.toRingHom =
      ψ₁.toAlgHom.toRingHom.comp d.baseMap.toAlgHom.toRingHom := by
    rw [← hψ₁]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfac]
    exact (flat_clopenRationalChart _ hC).comp (RingHom.Flat.of_bijective hbij)
  · intro z
    obtain ⟨c, hc⟩ := hbij.2 z
    obtain ⟨M, -, hlift⟩ := exists_lift_clopenRationalChart _ hC
    obtain ⟨c', hc', -⟩ := hlift c
    refine ⟨c', ?_⟩
    have := congrArg (fun φ : BoundedAlgHom K P.algebra Q.algebra => φ c') hψ₁
    simp only [BoundedAlgHom.comp_apply] at this
    rw [← this, hc', hc]

/-- Such a restriction is flat, unramified and of finite type at every point. -/
theorem restriction_isEtaleAtPoint (h : Q.locus ⊆ P.locus) (hC : IsClopen (P.chart ⁻¹' Q.locus))
    (s : BanachSpectrum Q.algebra) : (Q.restriction P h).IsEtaleAtPoint s := by
  obtain ⟨hflat, hsurj⟩ := Q.restriction_flat_and_surjective P h hC
  exact ⟨(Q.restriction P h).isFlatAtPoint_of_flat hflat s,
    (Q.restriction P h).isUnramifiedAtPoint_of_formallyUnramified
      (RingHom.FormallyUnramified.of_surjective hsurj) s⟩

theorem restriction_finite (h : Q.locus ⊆ P.locus) (hC : IsClopen (P.chart ⁻¹' Q.locus)) :
    (Q.restriction P h).toAlgHom.toRingHom.Finite :=
  RingHom.Finite.of_surjective _ (Q.restriction_flat_and_surjective P h hC).2

end RecognizedSubset

end IndexedAffinoidAtlas

end Langlands.Analytic
