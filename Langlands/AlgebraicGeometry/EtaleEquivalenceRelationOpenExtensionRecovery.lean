import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationOpenExtensionComparison
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Recovering a relation from its open part and a trivial complement -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.OpenExtension.Recovery

variable {E F : EtaleEquivalenceRelation.{u}}
    {f : E.U ⟶ F.U} {g : E.R ⟶ F.R} [IsOpenImmersion f]
    (h : IsCartesianHom E F f g)

/-- The canonical map from the arrow pushout back to the original relation. -/
noncomputable def toOriginal : arrows E f ⟶ F.R :=
  pushout.desc F.unit g (Comparison.unit_naturality h.1 h.2.w).symm

@[reassoc (attr := simp)]
lemma unit_toOriginal : unit E f ≫ toOriginal h = F.unit :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inclusion_toOriginal : inclusion E f ≫ toOriginal h = g :=
  pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
lemma toOriginal_t : toOriginal h ≫ F.t = t E f := by
  apply pushout.hom_ext
  · simp
  · simpa using h.1

@[reassoc (attr := simp)]
lemma toOriginal_s : toOriginal h ≫ F.s = s E f := by
  apply pushout.hom_ext
  · simp
  · simpa using h.2.w

instance mono_toOriginal : Mono (toOriginal h) where
  right_cancellation := by
    intro T a b hab
    apply OpenExtension.hom_ext E f
    · simpa only [Category.assoc, toOriginal_t] using congrArg (· ≫ F.t) hab
    · simpa only [Category.assoc, toOriginal_s] using congrArg (· ≫ F.s) hab

include h in
/-- The old arrow chart is open by the original source pullback square. -/
lemma isOpenImmersion_old : IsOpenImmersion g :=
  MorphismProperty.of_isPullback h.2.flip inferInstance

instance etale_toOriginal : Etale (toOriginal h) := by
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  let := isOpenImmersion_old h
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) (cover E f)
  intro i
  cases i <;> dsimp only [cover]
  · rw [unit_toOriginal]
    infer_instance
  · rw [inclusion_toOriginal]
    infer_instance

/-- The canonical pushout map is an open immersion. -/
instance isOpenImmersion_toOriginal : IsOpenImmersion (toOriginal h) :=
  IsOpenImmersion.of_flat_of_mono _

/-- Coverage by old arrows and units makes the canonical map surjective. -/
lemma surjective_of_cover
    (hc : ∀ r : F.R, r ∈ Set.range F.unit ∨ r ∈ Set.range g) :
    Surjective (toOriginal h) := by
  constructor
  intro r
  rcases hc r with ⟨x, hx⟩ | ⟨y, hy⟩
  · exact ⟨unit E f x, by
      simpa only [← Scheme.Hom.comp_apply, unit_toOriginal] using hx⟩
  · exact ⟨inclusion E f y, by
      simpa only [← Scheme.Hom.comp_apply, inclusion_toOriginal] using hy⟩

/-- The pushout recovers the original arrows when the two charts cover them. -/
lemma isIso_of_cover
    (hc : ∀ r : F.R, r ∈ Set.range F.unit ∨ r ∈ Set.range g) :
    IsIso (toOriginal h) :=
  (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨inferInstance, surjective_of_cover h hc⟩

variable {D : Scheme.{u}} (d : D ⟶ F.U)
    (hc : ∀ x : F.U, x ∉ Set.range f → x ∈ Set.range d)
    (hd : IsPullback (d ≫ F.unit) (𝟙 D) F.s d)

include h hc hd in
omit [IsOpenImmersion f] in
/-- A complement with trivial source relation gives coverage by units and
the old arrow scheme. Only point coverage is required of the complement map. -/
lemma cover_of_complement :
    ∀ r : F.R, r ∈ Set.range F.unit ∨ r ∈ Set.range g := by
  intro r
  by_cases hr : F.s r ∈ Set.range f
  · obtain ⟨x, hx⟩ := hr
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback h.2 r x hx.symm
    exact Or.inr ⟨z, hz⟩
  · obtain ⟨x, hx⟩ := hc (F.s r) hr
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback hd r x hx.symm
    exact Or.inl ⟨d z, by simpa only [Scheme.Hom.comp_apply] using hz⟩

include hc hd in
/-- The original relation is an open extension when its source relation
is trivial over a map covering the complement of the old open. -/
lemma isIso_of_complement : IsIso (toOriginal h) :=
  isIso_of_cover h (cover_of_complement h d hc hd)

/-- The actual arrow isomorphism recovering the original relation. -/
noncomputable def arrowsIso : arrows E f ≅ F.R := by
  let := isIso_of_complement h d hc hd
  exact asIso (toOriginal h)

@[simp]
lemma arrowsIso_hom : (arrowsIso h d hc hd).hom = toOriginal h := rfl

@[reassoc (attr := simp)]
lemma arrowsIso_inv_t : (arrowsIso h d hc hd).inv ≫ t E f = F.t := by
  rw [← toOriginal_t h, ← Category.assoc]
  exact (arrowsIso h d hc hd).inv_hom_id_assoc F.t

@[reassoc (attr := simp)]
lemma arrowsIso_inv_s : (arrowsIso h d hc hd).inv ≫ s E f = F.s := by
  rw [← toOriginal_s h, ← Category.assoc]
  exact (arrowsIso h d hc hd).inv_hom_id_assoc F.s

include hc hd in
/-- The recovery isomorphism gives a cartesian morphism with identity
map on objects. -/
lemma isCartesianHom :
    IsCartesianHom (relation E f) F (𝟙 F.U) (toOriginal h) := by
  let e := arrowsIso h d hc hd
  refine ⟨?_, ?_⟩
  · change toOriginal h ≫ F.t = t E f ≫ 𝟙 F.U
    rw [Category.comp_id]
    exact toOriginal_t h
  · change IsPullback (toOriginal h) (s E f) F.s (𝟙 F.U)
    refine IsPullback.mk' (by simp) ?_ ?_
    · intro T a b hm _
      let := isIso_of_complement h d hc hd
      exact (cancel_mono (toOriginal h)).mp hm
    · intro T a b hab
      refine ⟨a ≫ e.inv, ?_, ?_⟩
      · change (a ≫ e.inv) ≫ e.hom = a
        simp
      · simpa only [e, Category.assoc, arrowsIso_inv_s, Category.comp_id] using hab

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.OpenExtension.Recovery
