import Langlands.Geometry.Analytic.FinitePieceLocalMaps
import Langlands.Geometry.Analytic.RecognizedFinitePullback
import Langlands.Geometry.Analytic.ClopenPieceLocalization

/-! # Test maps out of the finite pieces of an affine analytification map -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification.FinitePieceLocal

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace IndexedAffinoidAtlas

/-- The restriction to a recognized subset that is clopen in a larger one kills exactly
the complement of an idempotent. -/
theorem exists_restriction_idempotent {K : Type u} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {X : Type v} [TopologicalSpace X]
    {a : IndexedAffinoidAtlas.{u, v, w} K X} (Q P : a.saturatedAtlas.RecognizedSubset)
    (h : Q.locus ⊆ P.locus) (hC : IsClopen (P.chart ⁻¹' Q.locus)) :
    ∃ e : P.algebra, IsIdempotentElem e ∧ Q.restriction P h e = 1 ∧
      ∀ x, Q.restriction P h x = 0 → e * x = 0 := by
  let d := clopenRationalChart (P.chart ⁻¹' Q.locus) hC
  have h₁ : Represents K d.baseMap (P.chart ⁻¹' Q.locus) := by
    have h0 : Represents K d.baseMap d.locus := d.toDomain.represents
    rwa [locus_clopenRationalChart] at h0
  have h₂ := Q.restriction_represents P h
  obtain ⟨ψ₁, hψ₁, -⟩ := h₁.2.2 _ (Q.restriction P h) h₂.hasImageIn
  obtain ⟨ψ₂, hψ₂, -⟩ := h₂.2.2 _ d.baseMap h₁.hasImageIn
  have hid₂ : ψ₂.comp ψ₁ = BoundedAlgHom.id K d.algebra :=
    (h₁.2.2 _ d.baseMap h₁.hasImageIn).unique
      (by rw [BoundedAlgHom.comp_assoc, hψ₁, hψ₂]) (BoundedAlgHom.id_comp _)
  have hinj : Function.Injective ψ₁ := Function.LeftInverse.injective (g := ψ₂) fun z =>
    congrArg (fun φ : BoundedAlgHom K d.algebra d.algebra => φ z) hid₂
  have hfac : ∀ x, Q.restriction P h x = ψ₁ (d.baseMap x) := fun x =>
    (congrArg (fun φ : BoundedAlgHom K P.algebra Q.algebra => φ x) hψ₁).symm
  obtain ⟨he, -, -⟩ := isClopenIdempotent_clopenIdempotent (P.chart ⁻¹' Q.locus) hC
  refine ⟨clopenIdempotent (P.chart ⁻¹' Q.locus) hC, he, ?_, fun x hx => ?_⟩
  · rw [hfac, baseMap_clopenIdempotent]
    exact map_one ψ₁.toAlgHom
  · apply clopenIdempotent_mul_eq_zero
    apply hinj
    rw [← hfac, hx]
    exact (map_zero ψ₁.toAlgHom).symm

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
  {B : Type w} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- Test maps out of a finite piece. Given a complete ultrametric normed `K`-algebra `E`,
a bounded map `τR` out of the algebra `R` of `W`, and a map `τB` out of `B` agreeing with
`τR` on `A`, there is an affinoid algebra `D` with maps `r : R → D` and `b : B → D`, a
surjective bounded map `ρ : D → S` onto the algebra of `V'` that is the restriction to an
idempotent `e`, and a bounded map `θ : D → E` extending `τR` and `τB`. Bounded maps out of
`D` are determined on the images of `r` and `b`. -/
theorem exists_test_factorization (V : Set (presentation K Q).space) (hVo : IsOpen V)
    (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset)
    (V' : (presentation K Q).atlas.saturatedAtlas.RecognizedSubset)
    (h : (saturatedHom K P Q f).baseMap '' range V'.chart ⊆ range W.chart)
    (hV' : V'.locus = V ∩ (saturatedHom K P Q f).baseMap ⁻¹' W.locus)
    (j₀ : (presentation K P).atlas.saturatedAtlas.Index)
    (hW₀ : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j₀))
    (i₀ : (presentation K Q).atlas.saturatedAtlas.Index)
    (hV₀ : V'.locus ⊆ range ((presentation K Q).atlas.saturatedAtlas.chart i₀))
    (E : Type*) [NormedCommRing E] [NormedAlgebra K E] [IsUltrametricDist E] [CompleteSpace E]
    (τR : BoundedAlgHom K W.algebra E) (τB : B →ₐ[K] E)
    (hτ : ∀ a, τB (f a) = τR (recMap P W j₀ hW₀ a)) :
    ∃ (D : PresentedAffinoidAlgebra K) (r : BoundedAlgHom K W.algebra D) (bm : B →ₐ[K] D)
      (ρ : BoundedAlgHom K D V'.algebra) (θ : BoundedAlgHom K D E) (e : D),
      (∀ x, ρ (r x) = (saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h x) ∧
      (∀ b, ρ (bm b) = recMap Q V' i₀ hV₀ b) ∧
      (∀ x, θ (r x) = τR x) ∧ (∀ b, θ (bm b) = τB b) ∧
      (∀ a, r (recMap P W j₀ hW₀ a) = bm (f a)) ∧
      IsIdempotentElem e ∧ ρ e = 1 ∧ (∀ x, ρ x = 0 → e * x = 0) ∧
      Function.Surjective ρ ∧
      ∀ (E' : Type u) [NormedCommRing E'] [NormedAlgebra K E'] (ψ ψ' : BoundedAlgHom K D E'),
        (∀ x, ψ (r x) = ψ' (r x)) → (∀ b, ψ (bm b) = ψ' (bm b)) → ψ = ψ' := by
  -- The source chart.
  obtain ⟨m₁, hm₁⟩ := exists_admits Q E τB
  obtain ⟨m₂, hm₂⟩ := exists_orig_superset Q (isCompact_recognized_locus V')
  let m := max m₁ m₂
  let i := origIndex Q (representative K Q m)
  have hVi : V'.locus ⊆ range ((presentation K Q).atlas.saturatedAtlas.chart i) :=
    hm₂ m (le_max_right _ _)
  obtain ⟨τi, hτi⟩ := exists_orig_lift Q E τB m (hm₁.mono Q E (le_max_left _ _))
  -- The target chart.
  have hZ : IsCompact (W.locus ∪ (saturatedHom K P Q f).baseMap ''
      range ((presentation K Q).atlas.saturatedAtlas.chart i)) :=
    (isCompact_recognized_locus W).union ((isCompact_range
      ((presentation K Q).atlas.saturatedAtlas.isEmbedding_chart i).continuous).image
        (saturatedHom K P Q f).baseMap.continuous)
  obtain ⟨m₃, hm₃⟩ := exists_orig_superset P hZ
  let j := origIndex P (representative K P m₃)
  have hjZ := hm₃ m₃ le_rfl
  have hW : W.locus ⊆ range ((presentation K P).atlas.saturatedAtlas.chart j) :=
    subset_union_left.trans hjZ
  have hij : (saturatedHom K P Q f).baseMap ''
      range ((presentation K Q).atlas.saturatedAtlas.chart i) ⊆
      range ((presentation K P).atlas.saturatedAtlas.chart j) :=
    subset_union_right.trans hjZ
  -- The pushout test algebra.
  have hcompat : τi.comp ((saturatedHom K P Q f).pullback i j hij) =
      τR.comp (W.containedRestriction j hW) := by
    apply orig_hom_ext P (representative K P m₃)
    intro a
    change τi ((saturatedHom K P Q f).pullback i j hij (satMap P j a)) = τR (recMap P W j hW a)
    rw [recMap_eq P W j j₀ hW hW₀, ← hτ, ← hτi]
    exact congrArg τi (LocalDomainMaps.saturatedHom_pullback_localAlgebraMap P Q f i j hij a)
  let φij := (saturatedHom K P Q f).pullback i j hij
  let r := AffinoidPushout.rightMap φij (W.containedRestriction j hW)
  let l := AffinoidPushout.leftMap φij (W.containedRestriction j hW)
  let bm : B →ₐ[K] AffinoidPushout.algebra φij (W.containedRestriction j hW) :=
    l.toAlgHom.comp (satMap Q i)
  let θ := AffinoidPushout.lift φij (W.containedRestriction j hW) E τi τR hcompat
  -- The recognized inverse image in the source chart.
  let V'' := AffinoidAtlasPresentation.StrongHom.recognizedPullback
    (A := presentation K Q) (B := presentation K P) (saturatedHom K P Q f) W i j hW hij
  have hpre : V''.locus = range ((presentation K Q).atlas.saturatedAtlas.chart i) ∩
      (saturatedHom K P Q f).baseMap ⁻¹' W.locus :=
    AffinoidAtlasPresentation.StrongHom.recognizedPullback_locus
      (A := presentation K Q) (B := presentation K P) (saturatedHom K P Q f) W i j hW hij
  have hV''i : V''.locus ⊆ range ((presentation K Q).atlas.saturatedAtlas.chart i) :=
    hpre.subset.trans inter_subset_left
  have hV'V'' : V'.locus ⊆ V''.locus := by
    intro x hx
    have hx' := hx
    rw [hV'] at hx'
    rw [hpre]
    exact ⟨hVi hx, hx'.2⟩
  have hVW'' : (saturatedHom K P Q f).baseMap '' range V''.chart ⊆ range W.chart :=
    AffinoidAtlasPresentation.StrongHom.recognizedPullback_admissible
      (A := presentation K Q) (B := presentation K P) (saturatedHom K P Q f) W i j hW hij
  let eqv := AffinoidAtlasPresentation.StrongHom.fullRecognitionPullbackEquiv
    (A := presentation K Q) (B := presentation K P) (saturatedHom K P Q f)
    V'' W i j hV''i hW hij hpre
  let ρ : BoundedAlgHom K (AffinoidPushout.algebra φij (W.containedRestriction j hW))
      V'.algebra := (V'.restriction V'' hV'V'').comp eqv.toBoundedAlgHom
  -- `ρ` on the right leg.
  have hρr : ∀ x, ρ (r x) = (saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h x := by
    intro x
    have e1 := congrArg (fun q => q x)
      (AffinoidAtlasPresentation.StrongHom.fullRecognitionPairs_pullback_eq_pushout
        (A := presentation K Q) (B := presentation K P) (saturatedHom K P Q f)
        V'' W i j hV''i hW hij hVW'' hpre)
    have hVr : range V'.chart ⊆ range V''.chart := by
      rw [V'.range_chart, V''.range_chart]
      exact hV'V''
    have e2 := (saturatedHom K P Q f).fullRecognitionPairs.restriction_comm V' V'' W W hVr
      Subset.rfl h hVW''
    change (V'.restriction V'' hV'V'').comp
        ((saturatedHom K P Q f).fullRecognitionPairs.pullback V'' W hVW'') =
      ((saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h).comp
        (W.restriction W Subset.rfl) at e2
    rw [W.restriction_self] at e2
    have e3 := congrArg (fun q => q x) e2
    exact (congrArg (V'.restriction V'' hV'V'') e1.symm).trans e3
  -- `ρ` on the left leg.
  have hρl : ρ.comp l = V'.containedRestriction i (hV'V''.trans hV''i) := by
    have hE : eqv.toBoundedAlgHom.comp l = V''.containedRestriction i hV''i :=
      Domain.boundedEquivOfLocusEq_comp_baseMap _ _ _
    rw [← V'.restriction_comp_containedRestriction V'' hV'V'' i hV''i, ← hE]
    rfl
  have hρbm : ∀ b, ρ (bm b) = recMap Q V' i₀ hV₀ b := by
    intro b
    rw [recMap_eq Q V' i₀ i hV₀ (hV'V''.trans hV''i)]
    exact congrArg (fun q => q (satMap Q i b)) hρl
  -- Idempotent.
  have hQ : V'.locus = V''.locus ∩ V := by
    apply Subset.antisymm
    · intro x hx
      have hx' := hx
      rw [hV'] at hx'
      exact ⟨hV'V'' hx, hx'.1⟩
    · rintro x ⟨hx, hxV⟩
      rw [hpre] at hx
      rw [hV']
      exact ⟨hxV, hx.2⟩
  have hC := V'.isClopen_chart_preimage_of_eq_inter V'' hVo hQ
  obtain ⟨e'', he'', he1, he0⟩ := exists_restriction_idempotent V' V'' hV'V'' hC
  have heqv : ∀ x, eqv.toBoundedAlgHom x = eqv.toAlgEquiv x := fun _ => rfl
  refine ⟨AffinoidPushout.algebra φij (W.containedRestriction j hW), r, bm, ρ, θ,
    eqv.toAlgEquiv.symm e'', hρr, hρbm, fun x => ?_, fun b => ?_, fun a => ?_,
    he''.map eqv.toAlgEquiv.symm, ?_, fun x hx => ?_, ?_, ?_⟩
  · exact congrArg (fun q => q x)
      (AffinoidPushout.lift_comp_rightMap φij (W.containedRestriction j hW) E τi τR hcompat)
  · rw [← hτi]
    exact congrArg (fun q => q (satMap Q i b))
      (AffinoidPushout.lift_comp_leftMap φij (W.containedRestriction j hW) E τi τR hcompat)
  · rw [recMap_eq P W j₀ j hW₀ hW]
    have e := congrArg (fun q => q (satMap P j a))
      (AffinoidPushout.condition φij (W.containedRestriction j hW))
    exact e.symm.trans
      (congrArg l (LocalDomainMaps.saturatedHom_pullback_localAlgebraMap P Q f i j hij a))
  · change V'.restriction V'' hV'V'' (eqv.toBoundedAlgHom (eqv.toAlgEquiv.symm e'')) = 1
    rw [heqv, AlgEquiv.apply_symm_apply]
    exact he1
  · apply eqv.toAlgEquiv.injective
    exact (map_mul eqv.toAlgEquiv _ x).trans
      ((congrArg (· * eqv.toAlgEquiv x) (eqv.toAlgEquiv.apply_symm_apply e'')).trans
        ((he0 _ hx).trans (map_zero eqv.toAlgEquiv).symm))
  · intro z
    obtain ⟨y, hy⟩ := (V'.restriction_flat_and_surjective V'' hV'V'' hC).2 z
    refine ⟨eqv.toAlgEquiv.symm y, ?_⟩
    change V'.restriction V'' hV'V'' (eqv.toBoundedAlgHom (eqv.toAlgEquiv.symm y)) = z
    rw [heqv, AlgEquiv.apply_symm_apply]
    exact hy
  · intro E' _ _ ψ ψ' hr hb
    apply AffinoidPushout.hom_ext φij (W.containedRestriction j hW) E' ψ ψ'
    · exact orig_hom_ext Q (representative K Q m) _ _ (fun b => hb b)
    · exact BoundedAlgHom.ext hr

end Langlands.Analytic.AffineAnalytification.FinitePieceLocal
