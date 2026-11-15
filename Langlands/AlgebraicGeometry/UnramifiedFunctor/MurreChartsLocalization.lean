import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreBaseChangeColimits
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps

/-! # Localizations as filtered colimits, and condition (F2)

A localization `M⁻¹A` is the filtered colimit of the rings `A[1/m]`, `m ∈ M`, ordered by
divisibility. With (F1a) and (F2), every element of `F(Spec M⁻¹A)` therefore comes from some
`F(Spec A[1/m])`, and two elements of `F(Spec A[1/m])` that agree on `Spec M⁻¹A` agree on some
`Spec A[1/mn]`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace Charts

section DivIndex

variable {A : Type u} [CommRing A] (M : Submonoid A)

/-- The elements of a submonoid `M`, preordered by divisibility. -/
def DivIndex : Type u := M

namespace DivIndex

variable {M}

/-- The element of `A` underlying an index. -/
abbrev val (a : DivIndex M) : A := (show M from a).1

lemma val_mem (a : DivIndex M) : a.val ∈ M := (show M from a).2

/-- The index given by an element of `M`. -/
abbrev mk (x : A) (hx : x ∈ M) : DivIndex M := show M from ⟨x, hx⟩

@[simp] lemma val_mk (x : A) (hx : x ∈ M) : (mk x hx).val = x := rfl

instance : Preorder (DivIndex M) where
  le a b := a.val ∣ b.val
  le_refl _ := dvd_refl _
  le_trans _ _ _ h₁ h₂ := dvd_trans h₁ h₂

lemma le_def {a b : DivIndex M} : a ≤ b ↔ a.val ∣ b.val := Iff.rfl

instance : IsDirected (DivIndex M) (· ≤ ·) :=
  ⟨fun a b ↦ ⟨mk (a.val * b.val) (M.mul_mem a.val_mem b.val_mem), dvd_mul_right _ _,
    dvd_mul_left _ _⟩⟩

instance : Nonempty (DivIndex M) := ⟨mk 1 M.one_mem⟩

end DivIndex

/-- For `a ∣ b`, the map `A[1/a] → A[1/b]`. -/
def awayMap {a b : A} (h : a ∣ b) : Localization.Away a →+* Localization.Away b :=
  IsLocalization.Away.lift a (isUnit_of_dvd_unit (map_dvd _ h)
    (IsLocalization.Away.algebraMap_isUnit b))

@[simp]
lemma awayMap_algebraMap {a b : A} (h : a ∣ b) (x : A) :
    awayMap h (algebraMap A _ x) = algebraMap A _ x :=
  IsLocalization.Away.lift_eq _ _ _

lemma awayMap_comp_algebraMap {a b : A} (h : a ∣ b) :
    (awayMap h).comp (algebraMap A _) = algebraMap A _ :=
  RingHom.ext (awayMap_algebraMap h)

lemma awayMap_id {a : A} : awayMap (dvd_refl a) = RingHom.id _ :=
  IsLocalization.ringHom_ext (Submonoid.powers a) (by rw [awayMap_comp_algebraMap]; rfl)

lemma awayMap_comp {a b c : A} (h₁ : a ∣ b) (h₂ : b ∣ c) :
    (awayMap h₂).comp (awayMap h₁) = awayMap (dvd_trans h₁ h₂) :=
  IsLocalization.ringHom_ext (Submonoid.powers a) (by
    rw [RingHom.comp_assoc, awayMap_comp_algebraMap, awayMap_comp_algebraMap,
      awayMap_comp_algebraMap])

/-- The diagram `a ↦ A[1/a]` of rings under `A`, indexed by `M` ordered by divisibility. -/
@[simps]
def awayDiagram : DivIndex M ⥤ Under (CommRingCat.of A) where
  obj a := Under.mk (CommRingCat.ofHom (algebraMap A (Localization.Away a.val)))
  map {a b} h := Under.homMk (CommRingCat.ofHom (awayMap (show a.val ∣ b.val from leOfHom h))) (by
    ext x
    exact awayMap_algebraMap (show a.val ∣ b.val from leOfHom h) x)
  map_id a := by
    ext x
    exact congrArg (fun φ : _ →+* _ ↦ φ x) awayMap_id
  map_comp {a b c} h₁ h₂ := by
    ext x
    exact (congrArg (fun φ : _ →+* _ ↦ φ x) (awayMap_comp (leOfHom h₁) (leOfHom h₂))).symm

variable (B : Type u) [CommRing B] [Algebra A B] [IsLocalization M B]

/-- The map `A[1/a] → M⁻¹A` for `a ∈ M`. -/
def toLoc (a : DivIndex M) : Localization.Away a.val →+* B :=
  IsLocalization.Away.lift a.val (IsLocalization.map_units B ⟨a.val, a.val_mem⟩)

@[simp]
lemma toLoc_algebraMap (a : DivIndex M) (x : A) :
    toLoc M B a (algebraMap A _ x) = algebraMap A B x :=
  IsLocalization.Away.lift_eq _ _ _

lemma toLoc_comp_awayMap {a b : DivIndex M} (h : a ≤ b) :
    (toLoc M B b).comp (awayMap h) = toLoc M B a :=
  IsLocalization.ringHom_ext (Submonoid.powers a.val) (by
    ext x
    simp)

/-- The cocone of the `A[1/a]` with vertex `M⁻¹A`. -/
@[simps]
def awayCocone : Cocone (awayDiagram M) where
  pt := Under.mk (CommRingCat.ofHom (algebraMap A B))
  ι :=
    { app a := Under.homMk (CommRingCat.ofHom (toLoc M B a)) (by
        ext x
        exact toLoc_algebraMap M B a x)
      naturality {a b} h := by
        ext x
        exact congrArg (fun φ : _ →+* _ ↦ φ x) (toLoc_comp_awayMap M B (leOfHom h)) }

lemma exists_toLoc_eq (x : B) : ∃ (a : DivIndex M) (y : Localization.Away a.val),
    toLoc M B a y = x := by
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  refine ⟨DivIndex.mk m.1 m.2, IsLocalization.mk' _ r
    (⟨m.1, Submonoid.mem_powers _⟩ : Submonoid.powers m.1), ?_⟩
  have hu : IsUnit (algebraMap A B m) := IsLocalization.map_units B m
  apply hu.mul_left_injective
  dsimp only
  rw [IsLocalization.mk'_spec]
  have := congrArg (toLoc M B (DivIndex.mk m.1 m.2))
    (IsLocalization.mk'_spec (Localization.Away m.1) r
      (⟨m.1, Submonoid.mem_powers _⟩ : Submonoid.powers m.1))
  rw [map_mul, toLoc_algebraMap, toLoc_algebraMap] at this
  exact this

lemma exists_awayMap_eq_zero {a : DivIndex M} (y : Localization.Away a.val)
    (hy : toLoc M B a y = 0) : ∃ (b : DivIndex M) (h : a ≤ b), awayMap h y = 0 := by
  obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers a.val) y
  have hr : algebraMap A B r = 0 := by
    have := congrArg (toLoc M B a) (IsLocalization.mk'_spec (Localization.Away a.val) r
      (⟨a.val ^ n, n, rfl⟩ : Submonoid.powers a.val))
    rw [map_mul, hy, zero_mul, toLoc_algebraMap] at this
    exact this.symm
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff M B r).1 hr
  have hab : a ≤ DivIndex.mk (a.val * c.1) (M.mul_mem a.val_mem c.2) := dvd_mul_right _ _
  refine ⟨_, hab, ?_⟩
  have hu₀ : IsUnit (algebraMap A (Localization.Away (a.val * c.1)) (a.val * c.1)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hcu : IsUnit (algebraMap A (Localization.Away (a.val * c.1)) c.1) :=
    isUnit_of_dvd_unit (map_dvd _ (dvd_mul_left _ _)) hu₀
  have hau : IsUnit (algebraMap A (Localization.Away (a.val * c.1)) (a.val ^ n)) := by
    rw [map_pow]
    exact (isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right _ _)) hu₀).pow n
  have hr' : algebraMap A (Localization.Away (a.val * c.1)) r = 0 := by
    apply hcu.mul_right_injective
    dsimp only
    rw [← map_mul, hc, map_zero, mul_zero]
  have key := congrArg (awayMap hab) (IsLocalization.mk'_spec (Localization.Away a.val) r
      (⟨a.val ^ n, n, rfl⟩ : Submonoid.powers a.val))
  rw [map_mul, awayMap_algebraMap, awayMap_algebraMap, hr'] at key
  exact hau.mul_left_eq_zero.1 key

lemma exists_awayMap_eq {a b : DivIndex M} (x : Localization.Away a.val)
    (y : Localization.Away b.val) (hxy : toLoc M B a x = toLoc M B b y) :
    ∃ (d : DivIndex M) (ha : a ≤ d) (hb : b ≤ d), awayMap ha x = awayMap hb y := by
  let c := DivIndex.mk (a.val * b.val) (M.mul_mem a.val_mem b.val_mem)
  have ha : a ≤ c := dvd_mul_right _ _
  have hb : b ≤ c := dvd_mul_left _ _
  have h0 : toLoc M B c (awayMap ha x - awayMap hb y) = 0 := by
    rw [map_sub, ← RingHom.comp_apply, ← RingHom.comp_apply, toLoc_comp_awayMap,
      toLoc_comp_awayMap, hxy, sub_self]
  obtain ⟨d, hcd, hd⟩ := exists_awayMap_eq_zero M B _ h0
  refine ⟨d, le_trans ha hcd, le_trans hb hcd, ?_⟩
  rw [map_sub, sub_eq_zero, ← RingHom.comp_apply, ← RingHom.comp_apply, awayMap_comp,
    awayMap_comp] at hd
  exact hd

/-- `M⁻¹A` is the filtered colimit of the `A[1/a]`, `a ∈ M`. -/
def awayCoconeIsColimit : IsColimit (awayCocone M B) := by
  haveI : ReflectsColimitsOfShape (DivIndex M) (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  haveI : IsConnected (DivIndex M) := IsFiltered.isConnected _
  apply isColimitOfReflects (Under.forget _)
  apply isColimitOfReflects (forget CommRingCat.{u})
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    obtain ⟨a, y, hy⟩ := exists_toLoc_eq M B x
    exact ⟨a, y, hy.symm⟩
  · intro a b x y hxy
    obtain ⟨d, ha, hb, h⟩ := exists_awayMap_eq M B x y hxy
    exact ⟨d, homOfLE ha, homOfLE hb, h⟩

end DivIndex

section F2

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
variable {A : Type u} [CommRing A] (M : Submonoid A)
variable (B : Type u) [CommRing B] [Algebra A B] [IsLocalization M B]

/-- (F2) for a localization: every element of `F(Spec M⁻¹A)` comes from some
`F(Spec A[1/a])`. -/
lemma exists_eq_of_isLocalization (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    (h : Spec (CommRingCat.of A) ⟶ S)
    (ζ : F.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ h)))) :
    ∃ (a : DivIndex M)
      (ζ' : F.obj (op (Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.val))) ≫ h)))),
      F.map ((BaseChange.specOver h).map ((awayCocone M B).ι.app a)) ζ' = ζ := by
  have := (BaseChange.good_all hZ h2 h).preserves_filtered_colimits (DivIndex M)
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (BaseChange.specOver h ⋙ F) (awayCoconeIsColimit M B)) ζ

/-- (F2) for a localization: two elements of `F(Spec A[1/a])` with the same image in
`F(Spec M⁻¹A)` have the same image in some `F(Spec A[1/b])`. -/
lemma exists_eq_of_isLocalization_of_eq (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    (h : Spec (CommRingCat.of A) ⟶ S) (a : DivIndex M)
    (ζ₁ ζ₂ : F.obj (op (Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.val))) ≫ h))))
    (heq : F.map ((BaseChange.specOver h).map ((awayCocone M B).ι.app a)) ζ₁ =
      F.map ((BaseChange.specOver h).map ((awayCocone M B).ι.app a)) ζ₂) :
    ∃ (b : DivIndex M) (hab : a ⟶ b),
      F.map ((BaseChange.specOver h).map ((awayDiagram M).map hab)) ζ₁ =
        F.map ((BaseChange.specOver h).map ((awayDiagram M).map hab)) ζ₂ := by
  have := (BaseChange.good_all hZ h2 h).preserves_filtered_colimits (DivIndex M)
  exact (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves
    (BaseChange.specOver h ⋙ F) (awayCoconeIsColimit M B)) ζ₁ ζ₂).1 heq

end F2

end Charts

end Langlands.AlgebraicGeometry.UnramifiedFunctor
