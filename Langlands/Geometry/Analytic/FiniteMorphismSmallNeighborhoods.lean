import Langlands.Geometry.Analytic.FullRecognitionEtaleMorphisms
import Langlands.Geometry.Analytic.AffinoidIdempotents
import Langlands.Geometry.Analytic.FiniteMorphismFibres
import Langlands.Geometry.Analytic.FibreSeparation
import Langlands.Geometry.Analytic.RecognizedDomainClosure

/-! # Arbitrarily small neighborhoods for finite morphisms -/

noncomputable section

universe u v w v' w'

namespace Langlands.Analytic

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace BoundedAlgHom

variable {R : Type v} {S : Type w} [NormedCommRing R] [NormedCommRing S]
  [NormedAlgebra K R] [NormedAlgebra K S]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- A bounded algebra map whose elements have norm-controlled preimages is a
finite Banach map with the single generator `1`. -/
theorem isFiniteBanach_of_lift (f : BoundedAlgHom K R S) {M : ℝ} (hM : 0 < M)
    (hlift : ∀ z : S, ∃ c : R, f c = z ∧ ‖c‖ ≤ M * ‖z‖) : f.IsFiniteBanach := by
  refine ⟨1, fun _ => 1, M, hM, fun z => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hlift z
  refine ⟨fun _ => c, ?_, ?_⟩
  · rw [coefficientMap_apply, Fin.sum_univ_one, mul_one, hc]
  · exact (pi_norm_le_iff_of_nonneg (mul_nonneg hM.le (norm_nonneg z))).2 fun _ => hcn

end BoundedAlgHom

namespace PresentedAffinoidAlgebra

variable {B : PresentedAffinoidAlgebra K}

/-- Norm-controlled preimages transfer between two maps that represent the
same subset of the spectrum. -/
theorem Represents.exists_lift_of_exists_lift {R₁ R₂ : PresentedAffinoidAlgebra K}
    {i₁ : BoundedAlgHom K B R₁} {i₂ : BoundedAlgHom K B R₂} {U : Set (BanachSpectrum B)}
    (h₁ : Represents K i₁ U) (h₂ : Represents K i₂ U) {M : ℝ} (hM : 0 < M)
    (hlift : ∀ z : R₁, ∃ c : B, i₁ c = z ∧ ‖c‖ ≤ M * ‖z‖) :
    ∃ M' : ℝ, 0 < M' ∧ ∀ z : R₂, ∃ c : B, i₂ c = z ∧ ‖c‖ ≤ M' * ‖z‖ := by
  obtain ⟨ψ₁, hψ₁, -⟩ := h₁.2.2 R₂ i₂ h₂.hasImageIn
  obtain ⟨ψ₂, hψ₂, -⟩ := h₂.2.2 R₁ i₁ h₁.hasImageIn
  have hid : ψ₁.comp ψ₂ = BoundedAlgHom.id K R₂ :=
    (h₂.2.2 R₂ i₂ h₂.hasImageIn).unique
      (by rw [BoundedAlgHom.comp_assoc, hψ₂, hψ₁]) (BoundedAlgHom.id_comp i₂)
  obtain ⟨C, hC, hψ₂b⟩ := ψ₂.bounded
  refine ⟨M * C, mul_pos hM hC, fun z => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hlift (ψ₂ z)
  refine ⟨c, ?_, ?_⟩
  · have h1 : i₂ c = ψ₁ (i₁ c) := by rw [← hψ₁]; rfl
    rw [h1, hc]
    exact congrArg (fun φ : BoundedAlgHom K R₂ R₂ => φ z) hid
  · calc ‖c‖ ≤ M * ‖ψ₂ z‖ := hcn
      _ ≤ M * (C * ‖z‖) := mul_le_mul_of_nonneg_left (hψ₂b z) hM.le
      _ = M * C * ‖z‖ := (mul_assoc _ _ _).symm

/-- The Weierstrass chart of a clopen subset has norm-controlled preimages:
glue an element on the chart with `0` on the complementary chart. -/
theorem exists_lift_clopenRationalChart (C : Set (BanachSpectrum B)) (hC : IsClopen C) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : (clopenRationalChart C hC).algebra,
      ∃ c : B, (clopenRationalChart C hC).baseMap c = z ∧ ‖c‖ ≤ M * ‖z‖ := by
  classical
  let d := clopenRationalChart C hC
  let d' := clopenRationalChart Cᶜ hC.compl
  let obj : Fin 2 → Domain K B := ![d.toDomain, d'.toDomain]
  let c : Domain.FiniteCover (Domain.whole K B) :=
    ⟨2, obj, fun i => Domain.inclusionOfSubset _ _ (Set.subset_univ _), fun x _ => by
      by_cases hx : x ∈ C
      · exact ⟨0, show x ∈ d.locus by rw [locus_clopenRationalChart]; exact hx⟩
      · exact ⟨1, show x ∈ d'.locus by rw [locus_clopenRationalChart]; exact hx⟩⟩
  have hres0 : (c.map 0).restriction = d.baseMap := Domain.restriction_toWhole (c.map 0)
  refine ⟨c.algebraRestrictionBound, c.algebraRestrictionBound_pos, fun z => ?_⟩
  let s : ∀ i : Fin c.size, (c.obj i).algebra := fun i =>
    Fin.cases (motive := fun i : Fin 2 => (obj i).algebra) z (fun _ => 0) i
  have hempty : ∀ (W : Domain K B), W.locus ⊆ C → W.locus ⊆ Cᶜ → Subsingleton W.algebra :=
    fun W h1 h2 => W.subsingleton_algebra_of_locus_eq_empty
      (Set.eq_empty_of_forall_notMem fun x hx => h2 hx (h1 hx))
  have hsub0 : ∀ (W : Domain K B), (W ⟶ c.obj 0) → W.locus ⊆ C := fun W f =>
    f.subset.trans (by change d.locus ⊆ C; rw [locus_clopenRationalChart])
  have hsub1 : ∀ (W : Domain K B), (W ⟶ c.obj 1) → W.locus ⊆ Cᶜ := fun W f =>
    f.subset.trans (by change d'.locus ⊆ Cᶜ; rw [locus_clopenRationalChart])
  have hs : c.AlgebraCompatible s := by
    intro i j W f g
    fin_cases i <;> fin_cases j
    · exact congrArg (fun h : Domain.Inclusion W (c.obj 0) => h.restriction (s 0))
        (Subsingleton.elim (α := Domain.Inclusion W _) f g)
    · have := hempty W (hsub0 W f) (hsub1 W g)
      exact Subsingleton.elim _ _
    · have := hempty W (hsub0 W g) (hsub1 W f)
      exact Subsingleton.elim _ _
    · exact congrArg (fun h : Domain.Inclusion W (c.obj 1) => h.restriction (s 1))
        (Subsingleton.elim (α := Domain.Inclusion W _) f g)
  obtain ⟨a, ha, -⟩ := c.algebra_existsUnique s hs
  refine ⟨a, ?_, ?_⟩
  · have h0 : (c.map 0).restriction a = s 0 := congrFun ha 0
    rw [hres0] at h0
    exact h0
  · refine (c.norm_le_algebraRestrictionBound a).trans
      (mul_le_mul_of_nonneg_left ?_ c.algebraRestrictionBound_pos.le)
    rw [ha]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun i => ?_
    fin_cases i
    · exact le_rfl
    · change ‖(0 : d'.algebra)‖ ≤ ‖z‖
      rw [norm_zero]
      exact norm_nonneg z

end PresentedAffinoidAlgebra

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- An open set that is relatively closed in a recognized subset pulls back to
a clopen subset of its spectrum. -/
theorem isClopen_chart_preimage (P : a.saturatedAtlas.RecognizedSubset) {O : Set X}
    (hO : IsOpen O) (hcl : P.locus ∩ closure O ⊆ O) : IsClopen (P.chart ⁻¹' O) := by
  refine ⟨?_, hO.preimage P.chart.continuous⟩
  have heq : P.chart ⁻¹' O = P.chart ⁻¹' closure O := by
    ext s
    constructor
    · exact fun h => subset_closure h
    · intro h
      exact hcl ⟨P.range_chart ▸ Set.mem_range_self s, h⟩
  rw [heq]
  exact isClosed_closure.preimage P.chart.continuous

/-- The recognized piece of a recognized subset cut out by an open set that is
relatively closed in it: the recognized local domain of the Weierstrass chart
of the clopen preimage in its spectrum. -/
def clopenPiece (P : a.saturatedAtlas.RecognizedSubset) {O : Set X} (hO : IsOpen O)
    (hcl : P.locus ∩ closure O ⊆ O) : a.saturatedAtlas.RecognizedSubset :=
  a.fullRecognitionDomainRecognizedSubset P
    (clopenRationalChart (P.chart ⁻¹' O) (a.isClopen_chart_preimage P hO hcl)).toDomain

theorem clopenPiece_locus (P : a.saturatedAtlas.RecognizedSubset) {O : Set X}
    (hO : IsOpen O) (hcl : P.locus ∩ closure O ⊆ O) :
    (a.clopenPiece P hO hcl).locus = P.locus ∩ O := by
  rw [clopenPiece, fullRecognitionDomainRecognizedSubset_locus]
  change P.chart '' (clopenRationalChart (P.chart ⁻¹' O) _).locus = _
  rw [locus_clopenRationalChart, Set.image_preimage_eq_inter_range, P.range_chart,
    Set.inter_comm]

theorem clopenPiece_subset (P : a.saturatedAtlas.RecognizedSubset) {O : Set X}
    (hO : IsOpen O) (hcl : P.locus ∩ closure O ⊆ O) :
    (a.clopenPiece P hO hcl).locus ⊆ P.locus := by
  rw [clopenPiece_locus]
  exact Set.inter_subset_left

/-- The restriction from a recognized subset to a clopen piece is a finite
Banach map. -/
theorem isFiniteBanach_restriction_clopenPiece (P : a.saturatedAtlas.RecognizedSubset)
    {O : Set X} (hO : IsOpen O) (hcl : P.locus ∩ closure O ⊆ O) :
    ((a.clopenPiece P hO hcl).restriction P
      (a.clopenPiece_subset P hO hcl)).IsFiniteBanach := by
  have hC := a.isClopen_chart_preimage P hO hcl
  obtain ⟨M, hM, hlift⟩ := exists_lift_clopenRationalChart (P.chart ⁻¹' O) hC
  have hrepD : Represents K (clopenRationalChart (P.chart ⁻¹' O) hC).baseMap (P.chart ⁻¹' O) := by
    have h0 : Represents K (clopenRationalChart (P.chart ⁻¹' O) hC).baseMap
        (clopenRationalChart (P.chart ⁻¹' O) hC).locus :=
      (clopenRationalChart (P.chart ⁻¹' O) hC).toDomain.represents
    rwa [locus_clopenRationalChart] at h0
  have hrep := (a.clopenPiece P hO hcl).restriction_represents P (a.clopenPiece_subset P hO hcl)
  have hloc : P.chart ⁻¹' (a.clopenPiece P hO hcl).locus = P.chart ⁻¹' O := by
    rw [clopenPiece_locus, Set.preimage_inter]
    have huniv : P.chart ⁻¹' P.locus = Set.univ := by
      rw [← P.range_chart]
      exact Set.preimage_range _
    rw [huniv, Set.univ_inter]
  rw [hloc] at hrep
  obtain ⟨M', hM', hlift'⟩ := Represents.exists_lift_of_exists_lift hrepD hrep hM hlift
  exact BoundedAlgHom.isFiniteBanach_of_lift _ hM' hlift'

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- Inside a finite morphism, the fibre over a point of a recognized target
subset is finite. -/
theorem IsFiniteOver.finite_fibre {V : Set A.space} {U : Set B.space}
    (hg : g.IsFiniteOver V U) (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (hWU : W.locus ⊆ U) {x : B.space} (hxW : x ∈ W.locus) :
    (V ∩ g.baseMap ⁻¹' {x}).Finite := by
  obtain ⟨P, h, hP, hfin⟩ := hg.2 W hWU
  have hxr : x ∈ Set.range W.chart := W.range_chart ▸ hxW
  obtain ⟨t, ht⟩ := hxr
  refine ((BoundedAlgHom.finite_fibre _ hfin.finite t).image P.chart).subset ?_
  rintro p ⟨hpV, hpx⟩
  have hpx' : g.baseMap p = x := hpx
  have hpP : p ∈ P.locus := hP ▸ ⟨hpV, show g.baseMap p ∈ W.locus from hpx' ▸ hxW⟩
  have hpr : p ∈ Set.range P.chart := P.range_chart ▸ hpP
  obtain ⟨s, rfl⟩ := hpr
  refine ⟨s, ?_, rfl⟩
  apply W.isEmbedding_chart.injective
  rw [ht]
  exact (g.fullRecognitionPairs.chart_comm P W h s).trans hpx'

/-- Berkovich's Lemma 3.1.2 for a finite morphism between open sets: the source
neighborhood of a point can be shrunk inside any prescribed neighborhood, with
a smaller open target over which the morphism is still finite. -/
theorem IsFiniteOver.exists_small {V : Set A.space} {U : Set B.space} (hV : IsOpen V)
    (hU : IsOpen U) (hg : g.IsFiniteOver V U) {y : A.space} (hy : y ∈ V)
    {V₀ : Set A.space} (hV₀ : V₀ ∈ 𝓝 y) :
    ∃ (V' : Set A.space) (U' : Set B.space), IsOpen V' ∧ IsOpen U' ∧ y ∈ V' ∧ V' ⊆ V₀ ∧
      V' ⊆ V ∧ U' ⊆ U ∧ g.IsFiniteOver V' U' := by
  have hxU : g.baseMap y ∈ U := hg.1 ⟨y, hy, rfl⟩
  obtain ⟨H, hH, hHt⟩ := B.atlas.locallyHausdorff (g.baseMap y)
  obtain ⟨I, hIfin, hIprop, hIN⟩ := B.atlas.exists_finite_recognized_nhds_subset (g.baseMap y)
    (interior H ∩ U) (Filter.inter_mem (interior_mem_nhds.2 hH) (hU.mem_nhds hxU))
  have : Finite I := hIfin.to_subtype
  have hIU : ∀ W ∈ I, W.locus ⊆ U := fun W hW => (hIprop W hW).2.trans Set.inter_subset_right
  have hIH : ∀ W ∈ I, W.locus ⊆ H := fun W hW =>
    (hIprop W hW).2.trans (Set.inter_subset_left.trans interior_subset)
  choose P hPh hP hPfin using fun W : I => hg.2 W.1 (hIU W.1 W.2)
  have hIne : I.Nonempty := by
    obtain ⟨W, hWI, -⟩ := Set.mem_iUnion₂.1 (mem_of_mem_nhds hIN)
    exact ⟨W, hWI⟩
  obtain ⟨W0, hW0⟩ := hIne
  have hF := hg.finite_fibre W0 (hIU W0 hW0) (hIprop W0 hW0).1
  have hN : (⋃ W : I, W.1.locus) ∈ 𝓝 (g.baseMap y) := by
    rw [Set.iUnion_subtype]
    exact hIN
  have hWc : ∀ W : B.atlas.saturatedAtlas.RecognizedSubset, IsCompact W.locus :=
    fun W => isCompact_iff_compactSpace.2 inferInstance
  have hQc : ∀ Q : A.atlas.saturatedAtlas.RecognizedSubset, IsCompact Q.locus :=
    fun Q => isCompact_iff_compactSpace.2 inferInstance
  have hQt : ∀ Q : A.atlas.saturatedAtlas.RecognizedSubset, T2Space Q.locus :=
    fun Q => inferInstance
  have hPc : ∀ W : I, IsCompact (V ∩ g.baseMap ⁻¹' W.1.locus) := fun W => hP W ▸ hQc (P W)
  have hPt : ∀ W : I, T2Space (V ∩ g.baseMap ⁻¹' W.1.locus : Set A.space) :=
    fun W => hP W ▸ hQt (P W)
  obtain ⟨O, 𝒰, ⟨hOopen, hOV, h𝒰open, hx𝒰, hcl⟩, hyO, hOV₀, h𝒰N⟩ :=
    @exists_isClopenOver_of_finite_fibre _ _ _ _ g.baseMap g.baseMap.continuous V hV
      (g.baseMap y) H hHt I _ (fun W : I => W.1.locus) (fun W => hWc W.1)
      (fun W => hIH W.1 W.2) (fun W => (hIprop W.1 W.2).1) hN hPc hPt hF y hy rfl V₀ hV₀
  have h𝒰U : 𝒰 ⊆ U := h𝒰N.trans (Set.iUnion_subset fun W => hIU W.1 W.2)
  refine ⟨O ∩ g.baseMap ⁻¹' 𝒰, 𝒰, hOopen.inter (h𝒰open.preimage g.baseMap.continuous),
    h𝒰open, ⟨hyO, hx𝒰⟩, Set.inter_subset_left.trans hOV₀, Set.inter_subset_left.trans hOV,
    h𝒰U, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hp.2
  · intro W'' hW''
    obtain ⟨P'', h'', hP'', hfin''⟩ := hg.2 W'' (hW''.trans h𝒰U)
    have hclP : P''.locus ∩ closure O ⊆ O := by
      rintro p ⟨hpP, hpcl⟩
      rw [hP''] at hpP
      exact hcl ⟨⟨hpP.1, hW'' hpP.2⟩, hpcl⟩
    have hQloc : (A.atlas.clopenPiece P'' hOopen hclP).locus =
        (O ∩ g.baseMap ⁻¹' 𝒰) ∩ g.baseMap ⁻¹' W''.locus := by
      refine (A.atlas.clopenPiece_locus P'' hOopen hclP).trans ?_
      ext p
      constructor
      · rintro ⟨hpP, hpO⟩
        have hpP' : p ∈ V ∩ g.baseMap ⁻¹' W''.locus := hP'' ▸ hpP
        exact ⟨⟨hpO, hW'' hpP'.2⟩, hpP'.2⟩
      · rintro ⟨⟨hpO, -⟩, hpW⟩
        have hpP' : p ∈ V ∩ g.baseMap ⁻¹' W''.locus := ⟨hOV hpO, hpW⟩
        exact ⟨hP''.symm ▸ hpP', hpO⟩
    have hQsub := A.atlas.clopenPiece_subset P'' hOopen hclP
    have hQr : Set.range (A.atlas.clopenPiece P'' hOopen hclP).chart ⊆ Set.range P''.chart := by
      rw [(A.atlas.clopenPiece P'' hOopen hclP).range_chart, P''.range_chart]
      exact hQsub
    have hQh : g.baseMap '' Set.range (A.atlas.clopenPiece P'' hOopen hclP).chart ⊆
        Set.range W''.chart := (Set.image_mono hQr).trans h''
    refine ⟨A.atlas.clopenPiece P'' hOopen hclP, hQh, hQloc, ?_⟩
    have hcomm := g.fullRecognitionPairs.restriction_comm (A.atlas.clopenPiece P'' hOopen hclP)
      P'' W'' W'' hQr (Set.Subset.refl _) hQh h''
    rw [B.fullRecognitionPresentation.atlas.restriction_id W'' (Set.Subset.refl _),
      BoundedAlgHom.comp_id] at hcomm
    rw [← hcomm]
    exact (A.atlas.isFiniteBanach_restriction_clopenPiece P'' hOopen hclP).comp hfin''

/-- Berkovich's Lemma 3.1.2: if `g` is finite at `y`, the neighborhoods can be
chosen inside any prescribed neighborhood of `y`. -/
theorem IsFiniteAt.exists_small {y : A.space} (hg : g.IsFiniteAt y) {V₀ : Set A.space}
    (hV₀ : V₀ ∈ 𝓝 y) :
    ∃ (V' : Set A.space) (U' : Set B.space), IsOpen V' ∧ IsOpen U' ∧ y ∈ V' ∧ V' ⊆ V₀ ∧
      g.IsFiniteOver V' U' := by
  obtain ⟨V, U, hV, hU, hy, hfin⟩ := hg
  obtain ⟨V', U', hV', hU', hy', hV'0, -, -, hfin'⟩ := hfin.exists_small hV hU hy hV₀
  exact ⟨V', U', hV', hU', hy', hV'0, hfin'⟩

/-- Restricting the target of a finite morphism to a smaller set keeps it
finite over the preimage. -/
theorem IsFiniteOver.restrictTarget {V : Set A.space} {U U' : Set B.space}
    (hg : g.IsFiniteOver V U) (hU' : U' ⊆ U) :
    g.IsFiniteOver (V ∩ g.baseMap ⁻¹' U') U' := by
  refine ⟨fun _ ⟨p, hp, hpx⟩ => hpx ▸ hp.2, fun W hW => ?_⟩
  obtain ⟨V', h, hV', hfin⟩ := hg.2 W (hW.trans hU')
  refine ⟨V', h, hV'.trans ?_, hfin⟩
  ext p
  constructor
  · rintro ⟨hpV, hpW⟩
    exact ⟨⟨hpV, hW hpW⟩, hpW⟩
  · rintro ⟨⟨hpV, -⟩, hpW⟩
    exact ⟨hpV, hpW⟩

variable {C : AffinoidAtlasPresentation.{u, v, w} K}
  {g' : StrongHom B.saturatedPresentation C.saturatedPresentation}

/-- Berkovich's Corollary 3.1.3 for compositions: finiteness at a point
composes. Lemma 3.1.2 shrinks the source neighborhood of the second map into
the target neighborhood of the first. -/
theorem IsFiniteAt.comp {y : A.space} (hg : g.IsFiniteAt y) (hg' : g'.IsFiniteAt (g.baseMap y)) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteAt y := by
  obtain ⟨V₁, U₁, hV₁, hU₁, hy, hfin⟩ := hg
  have hxU₁ : g.baseMap y ∈ U₁ := hfin.1 ⟨y, hy, rfl⟩
  obtain ⟨U₂, T, hU₂, hT, hx, hU₂U₁, hfin'⟩ := hg'.exists_small (hU₁.mem_nhds hxU₁)
  have hfin₁ := hfin.restrictTarget hU₂U₁
  exact ⟨V₁ ∩ g.baseMap ⁻¹' U₂, T, hV₁.inter (hU₂.preimage g.baseMap.continuous), hT,
    ⟨hy, hx⟩, hfin₁.comp hfin'⟩

/-- Quasifinite morphisms compose. -/
theorem IsQuasifinite.comp (hg : g.IsQuasifinite) (hg' : g'.IsQuasifinite) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsQuasifinite :=
  fun y => (hg y).comp (hg' (g.baseMap y))

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic
