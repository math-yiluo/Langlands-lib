import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteLocus
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Invariance of the maximal finite locus of an étale equivalence relation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasRelation

variable {U R : Scheme.{u}} {t s : R ⟶ U}

theorem IsEquivRel.hom_ext (h : IsEquivRel t s) {T : Scheme.{u}} {f g : T ⟶ R}
    (ht : f ≫ t = g ≫ t) (hs : f ≫ s = g ≫ s) : f = g := by
  have := h.mono
  rw [← cancel_mono (prod.lift t s)]
  apply prod.hom_ext <;> simp [ht, hs]

/-- Composition with an arrow identifies the two base changes of the source map. -/
theorem IsEquivRel.exists_isPullback_composition (h : IsEquivRel t s)
    {E : Scheme.{u}} (e : E ⟶ R) :
    ∃ c : Limits.pullback s (e ≫ t) ⟶ R,
      c ≫ t = pullback.fst s (e ≫ t) ≫ t ∧
      IsPullback c (pullback.snd s (e ≫ t)) s (e ≫ s) := by
  let P := Limits.pullback s (e ≫ t)
  let r : P ⟶ R := pullback.fst _ _
  let p : P ⟶ E := pullback.snd _ _
  have hw : r ≫ s = (p ≫ e) ≫ t := by
    simpa only [Category.assoc] using (pullback.condition (f := s) (g := e ≫ t))
  obtain ⟨c, hct, hcs⟩ := h.trans P r (p ≫ e) hw
  refine ⟨c, hct, IsPullback.mk' (by simpa only [Category.assoc] using hcs) ?_ ?_⟩
  · intro T f g hf hp
    apply pullback.hom_ext
    · apply h.hom_ext
      · change f ≫ r ≫ t = g ≫ r ≫ t
        rw [← hct, ← Category.assoc, ← Category.assoc, hf]
      · change f ≫ r ≫ s = g ≫ r ≫ s
        simpa only [hw, ← Category.assoc] using congrArg (· ≫ e ≫ t) hp
    · exact hp
  · intro T a b hab
    obtain ⟨v, hvt, hvs⟩ := h.symm T (b ≫ e)
    obtain ⟨d, hdt, hds⟩ := h.trans T a v (hab.trans hvt.symm)
    let l : T ⟶ P := pullback.lift d b (by simpa only [Category.assoc] using hds.trans hvs)
    refine ⟨l, ?_, by exact pullback.lift_snd _ _ _⟩
    apply h.hom_ext
    · rw [Category.assoc, hct]
      simpa only [l, r, pullback.lift_fst_assoc] using hdt
    · rw [Category.assoc, hcs]
      simpa only [l, p, Category.assoc, pullback.lift_snd_assoc] using hab.symm

/-- The open saturation of `W` under an étale relation. -/
def saturation (t s : R ⟶ U) [Etale t] (W : U.Opens) : U.Opens :=
  ⟨Set.range ((s ⁻¹ᵁ W).ι ≫ t), ((s ⁻¹ᵁ W).ι ≫ t).isOpenMap.isOpen_range⟩

/-- The projection over `t(s⁻¹ W)` is finite after the cover by `s⁻¹ W`. -/
theorem IsEquivRel.finite_composition_baseChange (h : IsEquivRel t s)
    (W : U.Opens) (hW : IsFinite (s ∣_ W)) :
    IsFinite (pullback.snd s ((s ⁻¹ᵁ W).ι ≫ t)) := by
  let E := (s ⁻¹ᵁ W).toScheme
  let e : E ⟶ R := (s ⁻¹ᵁ W).ι
  let P := Limits.pullback s (e ≫ t)
  let p : P ⟶ E := pullback.snd _ _
  obtain ⟨c, _, hc⟩ := h.exists_isPullback_composition e
  obtain ⟨c', hc'⟩ := exists_lift_preimage s W c (fun x ↦ by
    rw [← Scheme.Hom.comp_apply, hc.w, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact (p x).2)
  have hcp : c' ≫ s ∣_ W = p ≫ s ∣_ W := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, hc', Category.assoc, morphismRestrict_ι]
    exact hc.w
  have hcwhole : IsPullback (c' ≫ e) p s (s ∣_ W ≫ W.ι) := by
    rw [hc', morphismRestrict_ι]
    exact hc
  have hcpb : IsPullback c' p (s ∣_ W) (s ∣_ W) :=
    hcwhole.of_right hcp (isPullback_morphismRestrict s W).flip
  exact MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsFinite)
    hcpb hW

/-- Finiteness over an open propagates to its saturation under the relation. -/
theorem IsEquivRel.isFinite_restrict_saturation (h : IsEquivRel t s)
    [Etale t] [Etale s] [IsSeparated s] (W : U.Opens) (hW : IsFinite (s ∣_ W)) :
    IsFinite (s ∣_ saturation t s W) := by
  let E := (s ⁻¹ᵁ W).toScheme
  let e : E ⟶ R := (s ⁻¹ᵁ W).ι
  let V := saturation t s W
  let b : E ⟶ V.toScheme := _root_.AlgebraicGeometry.IsOpenImmersion.lift V.ι (e ≫ t) (by
    rw [Scheme.Opens.range_ι]
    exact fun _ hx ↦ hx)
  have hb : b ≫ V.ι = e ≫ t :=
    _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have : Etale (b ≫ V.ι) := by rw [hb]; infer_instance
  have : Etale b := Etale.of_comp b V.ι
  have : Surjective b := ⟨fun x ↦ by
    obtain ⟨y, hy⟩ := x.2
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change V.ι (b y) = V.ι x
    rw [← Scheme.Hom.comp_apply, hb]
    exact hy⟩
  let P := Limits.pullback s (e ≫ t)
  let r : P ⟶ R := pullback.fst _ _
  let p : P ⟶ E := pullback.snd _ _
  have hw : r ≫ s = p ≫ (e ≫ t) := pullback.condition
  obtain ⟨r', hr'⟩ := exists_lift_preimage s V r (fun x ↦ by
    rw [← Scheme.Hom.comp_apply, hw]
    exact ⟨p x, rfl⟩)
  have hpr : p ≫ b = r' ≫ s ∣_ V := by
    rw [← cancel_mono V.ι]
    simpa only [Category.assoc, hb, morphismRestrict_ι, ← hr'] using hw.symm
  have hwhole : IsPullback p (r' ≫ (s ⁻¹ᵁ V).ι) (b ≫ V.ι) s := by
    rw [hr', hb]
    exact (IsPullback.of_hasPullback s (e ≫ t)).flip
  have hpb : IsPullback p r' b (s ∣_ V) :=
    hwhole.of_bot hpr (isPullback_morphismRestrict s V)
  have : IsFinite p := h.finite_composition_baseChange W hW
  have : UniversallyClosed (s ∣_ V) :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @_root_.AlgebraicGeometry.UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hpb
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : IsProper (s ∣_ V) := {}
  have : LocallyQuasiFinite (s ∣_ V) := Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- Every maximal open of finiteness is invariant under an étale equivalence relation. -/
theorem IsEquivRel.invariant_of_maximal (h : IsEquivRel t s)
    [Etale t] [Etale s] [IsSeparated s] (W : U.Opens) (hW : IsFinite (s ∣_ W))
    (hmax : ∀ V : U.Opens, IsFinite (s ∣_ V) → V ≤ W) :
    s ⁻¹ᵁ W = t ⁻¹ᵁ W := by
  have hVW : saturation t s W ≤ W := hmax _ (h.isFinite_restrict_saturation W hW)
  have hinc : s ⁻¹ᵁ W ≤ t ⁻¹ᵁ W := by
    intro x hx
    exact hVW ⟨⟨x, hx⟩, rfl⟩
  refine le_antisymm hinc ?_
  obtain ⟨σ, hσt, hσs, _⟩ := h.exists_swap
  intro x hx
  have hx' : σ x ∈ s ⁻¹ᵁ W := by
    change s (σ x) ∈ W
    rw [← Scheme.Hom.comp_apply, hσs]
    exact hx
  have hx'' := hinc hx'
  change t (σ x) ∈ W at hx''
  rw [← Scheme.Hom.comp_apply, hσt] at hx''
  exact hx''

end Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasRelation


namespace Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteLocus

open AtlasRelation

/-- The finite locus of the separated source of an étale equivalence relation is invariant. -/
def FiniteLocusInvariantProp : Prop :=
  ∀ (U R : Scheme.{u}) (t s : R ⟶ U), IsEquivRel t s → Etale t → Etale s → IsSeparated s →
    s ⁻¹ᵁ finiteLocus s = t ⁻¹ᵁ finiteLocus s

/-- Finite-locus invariance with no quasi-compactness or Noetherian hypotheses. -/
theorem finiteLocus_invariant : FiniteLocusInvariantProp.{u} := by
  intro U R t s h ht hs hsep
  exact h.invariant_of_maximal (finiteLocus s) (isFinite_restrict_finiteLocus s)
    (fun _ hV ↦ le_finiteLocus s hV)

end Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteLocus
