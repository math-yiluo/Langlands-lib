import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationChartComparison

/-! # Invariant open subschemes of an étale equivalence relation -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- An open is invariant if an arrow has its source in the open exactly when
it has its target there. -/
def IsInvariantOpen (E : EtaleEquivalenceRelation.{u}) (U : E.U.Opens) : Prop :=
  E.s ⁻¹ᵁ U = E.t ⁻¹ᵁ U

variable (E : EtaleEquivalenceRelation.{u})

lemma isInvariantOpen_top : E.IsInvariantOpen ⊤ := by
  simp [IsInvariantOpen]

lemma isInvariantOpen_inf {U V : E.U.Opens}
    (hU : E.IsInvariantOpen U) (hV : E.IsInvariantOpen V) :
    E.IsInvariantOpen (U ⊓ V) := by
  change E.s ⁻¹ᵁ U = E.t ⁻¹ᵁ U at hU
  change E.s ⁻¹ᵁ V = E.t ⁻¹ᵁ V at hV
  simp only [IsInvariantOpen, Scheme.Hom.preimage_inf, hU, hV]

/-- Restriction to an invariant open is a cartesian relation morphism. -/
lemma isCartesianHom_chart_of_isInvariantOpen (U : E.U.Opens)
    (hU : E.IsInvariantOpen U) :
    IsCartesianHom (E.chart U.ι) E U.ι (Chart.map E U.ι) := by
  change Chart.map E U.ι ≫ E.t = Chart.t E U.ι ≫ U.ι ∧
    IsPullback (Chart.map E U.ι) (Chart.s E U.ι) E.s U.ι
  change E.s ⁻¹ᵁ U = E.t ⁻¹ᵁ U at hU
  refine ⟨Chart.map_t E U.ι, IsPullback.mk' (Chart.map_s E U.ι) ?_ ?_⟩
  · intro T a b hr hs
    apply Chart.hom_ext E U.ι
    · apply (cancel_mono U.ι).mp
      simpa only [Category.assoc, ← Chart.map_t] using congrArg (· ≫ E.t) hr
    · exact hs
  · intro T r v hv
    have hrange : Set.range (r ≫ E.t) ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      change r x ∈ E.t ⁻¹ᵁ U
      rw [← hU]
      change (r ≫ E.s) x ∈ U
      rw [hv]
      exact (v x).2
    let a := IsOpenImmersion.lift U.ι (r ≫ E.t) hrange
    have ha : a ≫ U.ι = r ≫ E.t := IsOpenImmersion.lift_fac _ _ _
    exact ⟨Chart.lift E U.ι a v r ha.symm hv, by simp, by simp⟩

namespace IsCartesianHom

variable {E F : EtaleEquivalenceRelation.{u}} {f : E.U ⟶ F.U} {g : E.R ⟶ F.R}
  (h : IsCartesianHom E F f g)

include h in
/-- Invariance is preserved by inverse image under a cartesian relation morphism. -/
lemma isInvariantOpen_preimage {U : F.U.Opens} (hU : F.IsInvariantOpen U) :
    E.IsInvariantOpen (f ⁻¹ᵁ U) := by
  change F.s ⁻¹ᵁ U = F.t ⁻¹ᵁ U at hU
  change E.s ⁻¹ᵁ (f ⁻¹ᵁ U) = E.t ⁻¹ᵁ (f ⁻¹ᵁ U)
  rw [← Scheme.Hom.comp_preimage, ← h.2.w, Scheme.Hom.comp_preimage,
    hU, ← Scheme.Hom.comp_preimage, h.1, Scheme.Hom.comp_preimage]

/-- The induced cartesian morphism of the open chart relations. -/
noncomputable def invariantOpenMap (U : F.U.Opens) :
    (E.chart (f ⁻¹ᵁ U).ι).R ⟶ (F.chart U.ι).R :=
  Chart.hom (f ⁻¹ᵁ U).ι U.ι (f ∣_ U) h.1 h.2.w
    (morphismRestrict_ι f U).symm

/-- The open chart comparison is cartesian; its object map is the actual
restriction of `f`. -/
lemma isCartesianHom_invariantOpenMap (U : F.U.Opens) :
    IsCartesianHom (E.chart (f ⁻¹ᵁ U).ι) (F.chart U.ι) (f ∣_ U)
      (h.invariantOpenMap U) :=
  Chart.isCartesianHom h (isPullback_morphismRestrict f U).flip

end IsCartesianHom

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
