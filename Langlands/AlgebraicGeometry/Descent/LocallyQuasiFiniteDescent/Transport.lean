import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic

/-! # Kernels of a represented base change -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent

open AlgebraicSpace

variable {S : Scheme.{u}} {F : Presheaf S} {T V W : Over S}
  {p : F ⟶ (schemeYoneda S).obj T} {g : V ⟶ T} {w : W ⟶ V}
  {c : (schemeYoneda S).obj W ⟶ F}

/-- Equality of the images of two points in a presheaf is equality after composing their
Yoneda morphisms with the given map. -/
theorem app_eq_app_iff {Z : Over S} (a b : Z ⟶ W) :
    c.app (op Z) ⟨a⟩ = c.app (op Z) ⟨b⟩ ↔
      (schemeYoneda S).map a ≫ c = (schemeYoneda S).map b ≫ c := by
  have key : ∀ x : Z ⟶ W,
      c.app (op Z) ⟨x⟩ = uliftYonedaEquiv ((schemeYoneda S).map x ≫ c) := by
    intro x
    rw [uliftYonedaEquiv_comp]
    simp
  rw [key, key, uliftYonedaEquiv.injective.eq_iff]

/-- In a represented base change, points of `W` are determined by their images in `F`
and in `V`. -/
theorem eq_of_isPullback
    (hpb : IsPullback c ((schemeYoneda S).map w) p ((schemeYoneda S).map g))
    {Z : Over S} {a b : Z ⟶ W}
    (hc : (schemeYoneda S).map a ≫ c = (schemeYoneda S).map b ≫ c) (hw : a ≫ w = b ≫ w) :
    a = b := by
  apply (schemeYoneda S).map_injective
  apply hpb.hom_ext hc
  rw [← Functor.map_comp, ← Functor.map_comp, hw]

/-- Points of `W` with the same image in `F` have the same image in `T`. -/
theorem comp_eq_of_comp_eq
    (hpb : IsPullback c ((schemeYoneda S).map w) p ((schemeYoneda S).map g))
    {Z : Over S} {a b : Z ⟶ W}
    (hc : (schemeYoneda S).map a ≫ c = (schemeYoneda S).map b ≫ c) :
    a ≫ w ≫ g = b ≫ w ≫ g := by
  apply (schemeYoneda S).map_injective
  have := congrArg (· ≫ p) hc
  simp only [Category.assoc, hpb.w] at this
  simpa only [Functor.map_comp] using this

/-- The first map `(W ×_T V) ×_T V ⟶ W ×_T V`, given by `(k₁ ∘ π₁, π₂)`. -/
def firstLift (w : W ⟶ V) (g : V ⟶ T) :
    pullback (pullback.snd (w ≫ g) g ≫ g) g ⟶ pullback (w ≫ g) g :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
    rw [Category.assoc, pullback.condition, pullback.condition])

theorem firstLift_fst :
    firstLift w g ≫ pullback.fst (w ≫ g) g = pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

theorem firstLift_snd :
    firstLift w g ≫ pullback.snd (w ≫ g) g = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

variable (hpb : IsPullback c ((schemeYoneda S).map w) p ((schemeYoneda S).map g))
include hpb

/-- The second map `W ×_T V ⟶ W`: it has the same image in `F` as the first projection
and lies over the second projection to `V`. -/
def secondMap : pullback (w ≫ g) g ⟶ W :=
  (schemeYoneda S).preimage
    (hpb.lift ((schemeYoneda S).map (pullback.fst (w ≫ g) g) ≫ c)
      ((schemeYoneda S).map (pullback.snd (w ≫ g) g))
      (by simp only [Category.assoc, hpb.w, ← Functor.map_comp, pullback.condition]))

theorem secondMap_c :
    (schemeYoneda S).map (secondMap hpb) ≫ c =
      (schemeYoneda S).map (pullback.fst (w ≫ g) g) ≫ c := by
  simp [secondMap]

theorem secondMap_w : secondMap hpb ≫ w = pullback.snd (w ≫ g) g := by
  apply (schemeYoneda S).map_injective
  simp [secondMap]

/-- If two points of `W` have the same image in `F`, they factor through the two maps
`W ×_T V ⟶ W`. -/
theorem exists_lift_of_comp_eq {Z : Over S} {a b : Z ⟶ W}
    (hc : (schemeYoneda S).map a ≫ c = (schemeYoneda S).map b ≫ c) :
    ∃ κ : Z ⟶ pullback (w ≫ g) g,
      κ ≫ pullback.fst (w ≫ g) g = a ∧ κ ≫ secondMap hpb = b := by
  refine ⟨pullback.lift a (b ≫ w) (by simpa [Category.assoc] using comp_eq_of_comp_eq hpb hc),
    pullback.lift_fst _ _ _, ?_⟩
  apply eq_of_isPullback hpb
  · rw [Functor.map_comp, Category.assoc, secondMap_c, ← Category.assoc, ← Functor.map_comp,
      pullback.lift_fst, hc]
  · rw [Category.assoc, secondMap_w, pullback.lift_snd]

/-- The diagonal `W ⟶ W ×_T V` is a section of the second map. -/
theorem diag_secondMap :
    pullback.lift (𝟙 W) w (by simp) ≫ secondMap hpb = 𝟙 W := by
  apply eq_of_isPullback hpb
  · rw [Functor.map_comp, Category.assoc, secondMap_c, ← Category.assoc, ← Functor.map_comp,
      pullback.lift_fst]
  · rw [Category.assoc, secondMap_w, pullback.lift_snd, Category.id_comp]

/-- The second map `(W ×_T V) ×_T V ⟶ W ×_T V`, given by `(k₂ ∘ π₁, π₂)`. -/
def secondLift :
    pullback (pullback.snd (w ≫ g) g ≫ g) g ⟶ pullback (w ≫ g) g :=
  pullback.lift (pullback.fst _ _ ≫ secondMap hpb) (pullback.snd _ _) (by
    rw [Category.assoc, ← Category.assoc (secondMap hpb), secondMap_w, pullback.condition])

theorem secondLift_fst :
    secondLift hpb ≫ pullback.fst (w ≫ g) g = pullback.fst _ _ ≫ secondMap hpb :=
  pullback.lift_fst _ _ _

theorem secondLift_snd :
    secondLift hpb ≫ pullback.snd (w ≫ g) g = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The cocycle identity `k₂ ∘ (k₁ ∘ π₁, π₂) = k₂ ∘ (k₂ ∘ π₁, π₂)`. -/
theorem firstLift_secondMap :
    firstLift w g ≫ secondMap hpb = secondLift hpb ≫ secondMap hpb := by
  apply eq_of_isPullback hpb
  · simp only [Functor.map_comp, Category.assoc, secondMap_c]
    simp only [← Functor.map_comp_assoc, firstLift_fst, secondLift_fst]
    simp only [Functor.map_comp, Category.assoc, secondMap_c]
  · rw [Category.assoc, Category.assoc, secondMap_w, firstLift_snd, secondLift_snd]

/-- Kernel comparison: suppose `q : W ⟶ Y` lies over `T`, identifies the two maps
`W ×_T V ⟶ W`, and is jointly monic with `w`. Then two points of `W` have the same
image in `F` exactly when they have the same image in `Y`. -/
theorem app_eq_app_iff_comp_eq {Y : Over S} (q : W ⟶ Y) (y : Y ⟶ T) (hy : q ≫ y = w ≫ g)
    (hq : pullback.fst (w ≫ g) g ≫ q = secondMap hpb ≫ q)
    (hmono : ∀ {Z : Over S} (a b : Z ⟶ W), a ≫ q = b ≫ q → a ≫ w = b ≫ w → a = b)
    (Z : Over S) (a b : Z ⟶ W) :
    c.app (op Z) ⟨a⟩ = c.app (op Z) ⟨b⟩ ↔ a ≫ q = b ≫ q := by
  rw [app_eq_app_iff]
  constructor
  · intro hc
    obtain ⟨κ, h₁, h₂⟩ := exists_lift_of_comp_eq hpb hc
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, hq]
  · intro hab
    have hwg : a ≫ w ≫ g = (b ≫ w) ≫ g := by
      simp only [Category.assoc]
      rw [← hy, reassoc_of% hab]
    let κ : Z ⟶ pullback (w ≫ g) g := pullback.lift a (b ≫ w) hwg
    have hκ : κ ≫ secondMap hpb = b := by
      apply hmono
      · rw [Category.assoc, ← hq, ← Category.assoc, pullback.lift_fst, hab]
      · rw [Category.assoc, secondMap_w, pullback.lift_snd]
    rw [← hκ, Functor.map_comp, Category.assoc, secondMap_c, ← Category.assoc,
      ← Functor.map_comp, pullback.lift_fst]

end Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent
