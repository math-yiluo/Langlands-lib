import Langlands.AlgebraicGeometry.DvrSmoothening.Points

/-! # Morphisms which are isomorphisms over an open, and resolved points -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- A morphism which is an isomorphism over an open is an isomorphism over every smaller open. -/
theorem isIso_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U)
    [IsIso (f ∣_ U)] : IsIso (f ∣_ V) := by
  have him : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr h
  have : IsIso (f ∣_ U ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  rw [← MorphismProperty.isomorphisms.iff] at this ⊢
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq f him)).mp this

/-- Composition of morphisms which are isomorphisms over an open and over its preimage. -/
theorem isIso_morphismRestrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    [h₁ : IsIso (g ∣_ U)] [h₂ : IsIso (f ∣_ g ⁻¹ᵁ U)] : IsIso ((f ≫ g) ∣_ U) := by
  rw [morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h₁

/-- Morphisms into an open over which `g` is an isomorphism lift along `g`. -/
theorem exists_lift_of_isIso {T X₁ X : Scheme.{u}} (g : X₁ ⟶ X) (W : X.Opens) [IsIso (g ∣_ W)]
    (a : T ⟶ X) (ha : Set.range a ⊆ W) :
    ∃ a₁ : T ⟶ X₁, a₁ ≫ g = a ∧ Set.range a₁ ⊆ g ⁻¹ᵁ W := by
  have ha' : Set.range a ⊆ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
  refine ⟨IsOpenImmersion.lift W.ι a ha' ≫ inv (g ∣_ W) ≫ (g ⁻¹ᵁ W).ι, ?_, ?_⟩
  · simp only [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      IsOpenImmersion.lift_fac]
  · rintro _ ⟨t, rfl⟩
    have : (g ⁻¹ᵁ W).ι ((IsOpenImmersion.lift W.ι a ha' ≫ inv (g ∣_ W)) t) ∈
        Set.range (g ⁻¹ᵁ W).ι := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at this
    simpa only [Scheme.Hom.comp_apply] using this

theorem smoothLocus_congr {X Y : Scheme.{u}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂)
    [LocallyOfFinitePresentation f₁] [LocallyOfFinitePresentation f₂] (x : X) :
    x ∈ f₁.smoothLocus ↔ x ∈ f₂.smoothLocus := by
  subst h
  rfl

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The points over the generic point of `Spec R` lie in the smooth locus. -/
def GenericallySmooth {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] : Prop :=
  ∀ x : X, (f x).asIdeal = ⊥ → x ∈ f.smoothLocus

theorem GenericallySmooth.comp {X X₁ : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    [LocallyOfFinitePresentation f] (hf : GenericallySmooth f) (g : X₁ ⟶ X)
    [LocallyOfFinitePresentation (g ≫ f)] (W : X.Opens) [IsIso (g ∣_ W)]
    (hW : ∀ x : X, (f x).asIdeal = ⊥ → x ∈ W) : GenericallySmooth (g ≫ f) := by
  intro x hx
  have hx' : (f (g x)).asIdeal = ⊥ := hx
  exact (mem_smoothLocus_comp_iff f g W x (hW _ hx')).mpr (hf _ hx')

/-- A point `P` is resolved by `g` if it lifts along `g` with closed point in the smooth locus. -/
def Resolved {X X₁ : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (g : X₁ ⟶ X)
    [LocallyOfFinitePresentation (g ≫ f)] (P : TestPoint X f) : Prop :=
  ∃ a₁ : Spec (CommRingCat.of P.ring) ⟶ X₁, a₁ ≫ g = P.a ∧
    a₁ (IsLocalRing.closedPoint P.ring) ∈ (g ≫ f).smoothLocus

/-- A resolved point stays resolved after a morphism which is an isomorphism over an open
containing the smooth locus. -/
theorem Resolved.comp {X X₁ X₂ : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {g : X₁ ⟶ X}
    [LocallyOfFinitePresentation (g ≫ f)] {P : TestPoint X f} (hP : Resolved g P)
    (h : X₂ ⟶ X₁) [LocallyOfFinitePresentation ((h ≫ g) ≫ f)] (W : X₁.Opens) [IsIso (h ∣_ W)]
    (hW : (g ≫ f).smoothLocus ≤ W) : Resolved (h ≫ g) P := by
  obtain ⟨a₁, ha₁, hs⟩ := hP
  have hr : Set.range a₁ ⊆ W := range_subset_of_closedPoint_mem a₁ W (hW hs)
  obtain ⟨a₂, ha₂, hr₂⟩ := exists_lift_of_isIso h W a₁ hr
  refine ⟨a₂, by rw [← Category.assoc, ha₂, ha₁], ?_⟩
  have : LocallyOfFinitePresentation (h ≫ g ≫ f) := by
    rw [← Category.assoc]; infer_instance
  have hx₁ : h (a₂ (IsLocalRing.closedPoint P.ring)) = a₁ (IsLocalRing.closedPoint P.ring) := by
    rw [← ha₂]; rfl
  have key := (mem_smoothLocus_comp_iff (g ≫ f) h W (a₂ (IsLocalRing.closedPoint P.ring))
    (hr₂ ⟨_, rfl⟩)).mpr (hx₁ ▸ hs)
  exact (smoothLocus_congr (Category.assoc h g f) _).mpr key

end Langlands.AlgebraicGeometry.DvrSmoothening
