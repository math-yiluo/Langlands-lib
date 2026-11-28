import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Translations

/-! # Slices of open immersions into `Y ×_S Y` and sections

Let `π : U' ⟶ Y ×_S Y` be an open immersion and `x` a `P`-valued point of `Y`. If the first
coordinate of `π` is `φ`, the scheme `pullback φ x` of pairs `(u, p)` with `φ u = x p` maps to
`Y ×_S P` by the second coordinate of `π` and `p`; this map is the base change of `π`, hence an
open immersion, and its image is dense in the fibres over `P` when the image of `π` is dense in
the fibres of the first projection. The same holds with the roles of the coordinates exchanged.

`HasSectionLifts g` says that every open subset of `Y ×_S P` dense in the fibres over `P` meets
the image of every point of `P` under some section of `g`; over a strictly henselian discrete
valuation ring this is `exists_section_lift_mem`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S}

section Slice

variable {U' P : Scheme.{u}} {q : P ⟶ S} (φ : U' ⟶ Y) (x : P ⟶ Y) (hx : x ≫ g = q)
  (π : U' ⟶ pullback g g)

include hx in
theorem slice_comp_aux (hπ : π ≫ pullback.fst g g = φ) :
    (pullback.fst φ x ≫ π ≫ pullback.snd g g) ≫ g = pullback.snd φ x ≫ q := by
  rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc π, hπ,
    ← Category.assoc, pullback.condition, Category.assoc, hx]

include hx in
theorem slice_comp_aux' (hπ : π ≫ pullback.snd g g = φ) :
    (pullback.fst φ x ≫ π ≫ pullback.fst g g) ≫ g = pullback.snd φ x ≫ q := by
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc π, hπ,
    ← Category.assoc, pullback.condition, Category.assoc, hx]

/-- `(u, p) ↦ (π₂ (π u), p)` on the scheme of pairs with `π₁ (π u) = x p`. -/
def sliceFst (hπ : π ≫ pullback.fst g g = φ) : pullback φ x ⟶ pullback g q :=
  pullback.lift (pullback.fst φ x ≫ π ≫ pullback.snd g g) (pullback.snd φ x)
    (slice_comp_aux φ x hx π hπ)

/-- `(u, p) ↦ (π₁ (π u), p)` on the scheme of pairs with `π₂ (π u) = x p`. -/
def sliceSnd (hπ : π ≫ pullback.snd g g = φ) : pullback φ x ⟶ pullback g q :=
  pullback.lift (pullback.fst φ x ≫ π ≫ pullback.fst g g) (pullback.snd φ x)
    (slice_comp_aux' φ x hx π hπ)

@[reassoc (attr := simp)]
theorem sliceFst_fst (hπ : π ≫ pullback.fst g g = φ) :
    sliceFst φ x hx π hπ ≫ pullback.fst g q = pullback.fst φ x ≫ π ≫ pullback.snd g g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sliceFst_snd (hπ : π ≫ pullback.fst g g = φ) :
    sliceFst φ x hx π hπ ≫ pullback.snd g q = pullback.snd φ x :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem sliceSnd_fst (hπ : π ≫ pullback.snd g g = φ) :
    sliceSnd φ x hx π hπ ≫ pullback.fst g q = pullback.fst φ x ≫ π ≫ pullback.fst g g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sliceSnd_snd (hπ : π ≫ pullback.snd g g = φ) :
    sliceSnd φ x hx π hπ ≫ pullback.snd g q = pullback.snd φ x :=
  pullback.lift_snd _ _ _

theorem isPullback_sliceFst (hπ : π ≫ pullback.fst g g = φ) :
    IsPullback (pullback.fst φ x) (sliceFst φ x hx π hπ) π (pairFst x hx) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_pairFst x hx)
  · rw [sliceFst_snd, hπ]
    exact IsPullback.of_hasPullback φ x
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, sliceFst_snd_assoc]
      rw [hπ, pullback.condition]
    · simp only [Category.assoc, pullback.lift_snd, sliceFst_fst]

theorem isPullback_sliceSnd (hπ : π ≫ pullback.snd g g = φ) :
    IsPullback (pullback.fst φ x) (sliceSnd φ x hx π hπ) π (pairSnd x hx) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_pairSnd x hx)
  · rw [sliceSnd_snd, hπ]
    exact IsPullback.of_hasPullback φ x
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, sliceSnd_fst]
    · simp only [Category.assoc, pullback.lift_snd, sliceSnd_snd_assoc]
      rw [hπ, pullback.condition]

variable [IsOpenImmersion π]

instance (hπ : π ≫ pullback.fst g g = φ) : IsOpenImmersion (sliceFst φ x hx π hπ) :=
  MorphismProperty.of_isPullback (isPullback_sliceFst φ x hx π hπ) inferInstance

instance (hπ : π ≫ pullback.snd g g = φ) : IsOpenImmersion (sliceSnd φ x hx π hπ) :=
  MorphismProperty.of_isPullback (isPullback_sliceSnd φ x hx π hπ) inferInstance

omit [IsOpenImmersion π] in
theorem range_sliceFst (hπ : π ≫ pullback.fst g g = φ) :
    Set.range (sliceFst φ x hx π hπ) = pairFst x hx ⁻¹' Set.range π := by
  have h := Scheme.image_preimage_eq_of_isPullback (isPullback_sliceFst φ x hx π hπ) Set.univ
  rwa [Set.preimage_univ, Set.image_univ, Set.image_univ] at h

omit [IsOpenImmersion π] in
theorem range_sliceSnd (hπ : π ≫ pullback.snd g g = φ) :
    Set.range (sliceSnd φ x hx π hπ) = pairSnd x hx ⁻¹' Set.range π := by
  have h := Scheme.image_preimage_eq_of_isPullback (isPullback_sliceSnd φ x hx π hπ) Set.univ
  rwa [Set.preimage_univ, Set.image_univ, Set.image_univ] at h

theorem fibreGenerizationDense_range_sliceFst (hπ : π ≫ pullback.fst g g = φ)
    (hd : FibreGenerizationDense (pullback.fst g g) (Set.range π)) :
    FibreGenerizationDense (pullback.snd g q) (Set.range (sliceFst φ x hx π hπ)) := by
  rw [range_sliceFst]
  exact fibreGenerizationDense_pairFst x hx hd

theorem fibreGenerizationDense_range_sliceSnd (hπ : π ≫ pullback.snd g g = φ)
    (hd : FibreGenerizationDense (pullback.snd g g) (Set.range π)) :
    FibreGenerizationDense (pullback.snd g q) (Set.range (sliceSnd φ x hx π hπ)) := by
  rw [range_sliceSnd]
  exact fibreGenerizationDense_pairSnd x hx hd

end Slice

/-- The image under an open immersion with fibrewise dense range of a fibrewise dense set is
fibrewise dense. -/
theorem fibreGenerizationDense_image {A E P : Scheme.{u}} (s : A ⟶ E) [IsOpenImmersion s]
    (pE : E ⟶ P) (hs : FibreGenerizationDense pE (Set.range s)) {Z : Set A}
    (hZ : FibreGenerizationDense (s ≫ pE) Z) : FibreGenerizationDense pE (s '' Z) := by
  intro e
  obtain ⟨_, ⟨a₁, rfl⟩, he₁, he₁e⟩ := hs e
  obtain ⟨a₂, ha₂, ha₂₁, ha₂a₁⟩ := hZ a₁
  refine ⟨s a₂, ⟨a₂, ha₂, rfl⟩, ?_, (ha₂a₁.map s.continuous).trans he₁e⟩
  rw [← he₁]
  simpa only [Scheme.Hom.comp_apply] using ha₂₁

/-- The sections of `g`. -/
abbrev Sect (g : Y ⟶ S) : Type u := {c : S ⟶ Y // c ≫ g = 𝟙 S}

/-- The point `(c (q p), p)` of `Y ×_S P` attached to a section `c` and a point `p` of `P`. -/
abbrev secLift {P : Scheme.{u}} (q : P ⟶ S) (c : Sect g) : P ⟶ pullback g q :=
  pullback.lift (q ≫ c.1) (𝟙 P) (by rw [Category.assoc, c.2, Category.comp_id, Category.id_comp])

/-- Every open subset of `Y ×_S P` dense in the fibres over `P` contains `(c (q p), p)` for some
section `c`, for every point `p` of `P`. -/
def HasSectionLifts (g : Y ⟶ S) : Prop :=
  ∀ (P : Scheme.{u}) (q : P ⟶ S) (Z : Set ↥(pullback g q)), IsOpen Z →
    FibreGenerizationDense (pullback.snd g q) Z → ∀ p : P, ∃ c : Sect g, secLift q c p ∈ Z

/-- Section lifts in morphism form: for an open immersion into `Y ×_S P` with fibrewise dense
image and a point `p`, some section lifts on a neighbourhood of `p`. -/
theorem HasSectionLifts.exists_lift (hg : HasSectionLifts g) {P Zs : Scheme.{u}} (q : P ⟶ S)
    (j : Zs ⟶ pullback g q) [IsOpenImmersion j]
    (hj : FibreGenerizationDense (pullback.snd g q) (Set.range j)) (p : P) :
    ∃ (c : Sect g) (O : P.Opens) (ℓ : O.toScheme ⟶ Zs), p ∈ O ∧ ℓ ≫ j = O.ι ≫ secLift q c := by
  obtain ⟨c, hc⟩ := hg P q (Set.range j) j.isOpenEmbedding.isOpen_range hj p
  set O : P.Opens := secLift q c ⁻¹ᵁ j.opensRange
  have hr : Set.range (O.ι ≫ secLift q c) ⊆ Set.range j := by
    rintro _ ⟨t, rfl⟩
    exact t.2
  exact ⟨c, O, IsOpenImmersion.lift j _ hr, hc, IsOpenImmersion.lift_fac _ _ _⟩

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
