import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # The fppf sheaf quotient of an equivalence relation on points

For morphisms `t s : R ⟶ U` of schemes over `S` whose points form an equivalence relation, with
`R` embedded in pairs of points of `U`, we form the presheaf quotient of the functor of points of
`U` by the relation and its fppf sheafification `Q`. The quotient map `a : U ⟶ Q` is locally
surjective and its kernel pair is `(t, s)`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.RelationQuotient

variable {S : Scheme.{u}} {U R : Over S}

/-- The points of `R` over every scheme `T` over `S` form an equivalence relation on the points
of `U` via `(t, s)`, and a point of `R` is determined by its two projections. -/
structure IsOverEquivRel (t s : R ⟶ U) : Prop where
  ext : ∀ ⦃T : Over S⦄ (r r' : T ⟶ R), r ≫ t = r' ≫ t → r ≫ s = r' ≫ s → r = r'
  refl : ∀ ⦃T : Over S⦄ (x : T ⟶ U), ∃ r : T ⟶ R, r ≫ t = x ∧ r ≫ s = x
  symm : ∀ ⦃T : Over S⦄ (r : T ⟶ R), ∃ r' : T ⟶ R, r' ≫ t = r ≫ s ∧ r' ≫ s = r ≫ t
  trans : ∀ ⦃T : Over S⦄ (r r' : T ⟶ R), r ≫ s = r' ≫ t →
    ∃ r'' : T ⟶ R, r'' ≫ t = r ≫ t ∧ r'' ≫ s = r' ≫ s

/-- Two `T`-points of `U` are related when they are the projections of a `T`-point of `R`. -/
def PointRel (t s : R ⟶ U) (T : Over S) (x y : ULift.{u + 1} (T ⟶ U)) : Prop :=
  ∃ r : T ⟶ R, r ≫ t = x.down ∧ r ≫ s = y.down

theorem PointRel.comp {t s : R ⟶ U} {T T' : Over S} (g : T' ⟶ T) {x y : ULift.{u + 1} (T ⟶ U)}
    (h : PointRel t s T x y) : PointRel t s T' ⟨g ≫ x.down⟩ ⟨g ≫ y.down⟩ := by
  obtain ⟨r, hr₁, hr₂⟩ := h
  exact ⟨g ≫ r, by rw [Category.assoc, hr₁], by rw [Category.assoc, hr₂]⟩

theorem IsOverEquivRel.equivalence {t s : R ⟶ U} (h : IsOverEquivRel t s) (T : Over S) :
    Equivalence (PointRel t s T) where
  refl x := h.refl x.down
  symm := by
    rintro x y ⟨r, h₁, h₂⟩
    obtain ⟨r', h₃, h₄⟩ := h.symm r
    exact ⟨r', h₃.trans h₂, h₄.trans h₁⟩
  trans := by
    rintro x y z ⟨r, h₁, h₂⟩ ⟨r', h₃, h₄⟩
    obtain ⟨r'', h₅, h₆⟩ := h.trans r r' (h₂.trans h₃.symm)
    exact ⟨r'', h₅.trans h₁, h₆.trans h₄⟩

variable (t s : R ⟶ U)

/-- The presheaf quotient of the points of `U` by the relation `(t, s)`. -/
def quotientPresheaf : Presheaf S where
  obj T := Quot (PointRel t s T.unop)
  map g := ↾(Quot.map (fun x => ⟨g.unop ≫ x.down⟩) fun _ _ h => h.comp g.unop)
  map_id T := by
    ext q
    induction q using Quot.ind with
    | mk x => exact congrArg (Quot.mk _) (congrArg ULift.up (Category.id_comp x.down))
  map_comp f g := by
    ext q
    induction q using Quot.ind with
    | mk x => exact congrArg (Quot.mk _) (congrArg ULift.up (Category.assoc _ _ x.down))

/-- The projection from the points of `U` to the presheaf quotient. -/
def quotientπ : (schemeYoneda S).obj U ⟶ quotientPresheaf t s where
  app T := ↾fun x => Quot.mk _ x

/-- The fppf sheaf quotient of the points of `U` by the relation `(t, s)`. -/
abbrev quotientSheaf : FppfSheaf S :=
  (presheafToSheaf (fppfTopology S) (Type (u + 1))).obj (quotientPresheaf t s)

/-- The quotient map from the points of `U` to the fppf sheaf quotient. -/
def quotientMap : (schemeYoneda S).obj U ⟶ (quotientSheaf t s).obj :=
  quotientπ t s ≫ CategoryTheory.toSheafify (fppfTopology S) (quotientPresheaf t s)

theorem quotientπ_app_eq_iff {t s : R ⟶ U} (h : IsOverEquivRel t s) {T : Over S}
    (x y : ULift.{u + 1} (T ⟶ U)) :
    (quotientπ t s).app (op T) x = (quotientπ t s).app (op T) y ↔ PointRel t s T x y := by
  constructor
  · intro hxy
    exact (h.equivalence T).eqvGen_iff.1 (Quot.eqvGen_exact hxy)
  · intro hxy
    exact Quot.sound hxy

theorem quotientπ_w : (schemeYoneda S).map t ≫ quotientπ t s =
    (schemeYoneda S).map s ≫ quotientπ t s := by
  ext T r
  exact Quot.sound ⟨r.down, rfl, rfl⟩

theorem quotientMap_w : (schemeYoneda S).map t ≫ quotientMap t s =
    (schemeYoneda S).map s ≫ quotientMap t s := by
  rw [quotientMap, ← Category.assoc, quotientπ_w, Category.assoc]

/-- The projection to the presheaf quotient is surjective on sections. -/
theorem quotientπ_surjective (T : (Over S)ᵒᵖ) : Function.Surjective ((quotientπ t s).app T) := by
  intro q
  induction q using Quot.ind with
  | mk x => exact ⟨x, rfl⟩

/-- The quotient map is fppf locally surjective. -/
instance isLocallySurjective_quotientMap :
    Presheaf.IsLocallySurjective (fppfTopology S) (quotientMap t s) := by
  have : Presheaf.IsLocallySurjective (fppfTopology S) (quotientπ t s) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (quotientπ_surjective t s)
  unfold quotientMap
  infer_instance

/-- Two `T`-points of `U` with the same image in the sheaf quotient are the projections of a
`T`-point of `R`: they are related locally, and the local relating points glue in `R`. -/
theorem exists_of_quotientMap_eq {t s : R ⟶ U} (h : IsOverEquivRel t s) {T : Over S}
    (x y : T ⟶ U)
    (hxy : (quotientMap t s).app (op T) ⟨x⟩ = (quotientMap t s).app (op T) ⟨y⟩) :
    ∃ r : T ⟶ R, r ≫ t = x ∧ r ≫ s = y := by
  let J := Presheaf.equalizerSieve (F := quotientPresheaf t s) (X := op T)
    ((quotientπ t s).app (op T) ⟨x⟩) ((quotientπ t s).app (op T) ⟨y⟩)
  have hJ : J ∈ fppfTopology S T :=
    Presheaf.equalizerSieve_mem (fppfTopology S)
      (CategoryTheory.toSheafify (fppfTopology S) (quotientPresheaf t s)) _ _ hxy
  have hloc : ∀ ⦃T' : Over S⦄ (u : T' ⟶ T), J u →
      ∃ r : T' ⟶ R, r ≫ t = u ≫ x ∧ r ≫ s = u ≫ y := fun T' u hu ↦
    (quotientπ_app_eq_iff h ⟨u ≫ x⟩ ⟨u ≫ y⟩).1 hu
  choose k hk₁ hk₂ using hloc
  have hR := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := fppfTopology S) (yoneda.obj R) J hJ
  have hU := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := fppfTopology S) (yoneda.obj U) J hJ
  let f : Presieve.FamilyOfElements (yoneda.obj R) J.arrows := fun _ u hu ↦ k u hu
  have hf : f.Compatible := by
    intro T₁ T₂ T₃ a₁ a₂ u₁ u₂ hu₁ hu₂ e
    change a₁ ≫ k u₁ hu₁ = a₂ ≫ k u₂ hu₂
    apply h.ext
    · rw [Category.assoc, Category.assoc, hk₁, hk₁, ← Category.assoc, ← Category.assoc, e]
    · rw [Category.assoc, Category.assoc, hk₂, hk₂, ← Category.assoc, ← Category.assoc, e]
  have hglue : ∀ ⦃T' : Over S⦄ (u : T' ⟶ T) (hu : J u), u ≫ hR.amalgamate f hf = k u hu :=
    fun _ u hu ↦ hR.valid_glue hf u hu
  refine ⟨hR.amalgamate f hf, hU.isSeparatedFor.ext fun T' u hu ↦ ?_,
    hU.isSeparatedFor.ext fun T' u hu ↦ ?_⟩
  · change u ≫ (hR.amalgamate f hf ≫ t) = u ≫ x
    rw [← Category.assoc, hglue u hu, hk₁]
  · change u ≫ (hR.amalgamate f hf ≫ s) = u ≫ y
    rw [← Category.assoc, hglue u hu, hk₂]

/-- The kernel pair of the quotient map is `(t, s)`. -/
theorem isPullback_quotientMap {t s : R ⟶ U} (h : IsOverEquivRel t s) :
    IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) (quotientMap t s)
      (quotientMap t s) := by
  refine IsPullback.of_forall_isPullback_app fun T ↦ ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [← NatTrans.comp_app, ← NatTrans.comp_app, quotientMap_w]
  · rintro ⟨r⟩ ⟨r'⟩ ⟨h₁, h₂⟩
    exact congrArg ULift.up (h.ext r r' (congrArg ULift.down h₁) (congrArg ULift.down h₂))
  · rintro ⟨x⟩ ⟨y⟩ hxy
    obtain ⟨r, hr₁, hr₂⟩ := exists_of_quotientMap_eq h x y hxy
    exact ⟨⟨r⟩, congrArg ULift.up hr₁, congrArg ULift.up hr₂⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.RelationQuotient
