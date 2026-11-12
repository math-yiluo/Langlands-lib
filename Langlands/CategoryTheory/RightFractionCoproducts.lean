import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Coproducts in localizations with a right calculus of fractions -/

noncomputable section

universe w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace Langlands.CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- Chosen coproducts in `C` of replaced families, compatible with `W`. Every object `T` has
a replacement `replace T` with a morphism `π T : replace T ⟶ T` in `W`; every family of
replacements has a chosen colimit cofan; and the morphism induced on chosen coproducts by a
family of morphisms in `W` is in `W`. -/
structure RightFractionCoproducts (W : MorphismProperty C) (J : Type w) where
  /-- The replacement of an object. -/
  replace : C → C
  /-- The comparison morphism of the replacement. -/
  π : ∀ T, replace T ⟶ T
  π_mem : ∀ T, W (π T)
  /-- The chosen coproduct of a family of replacements. -/
  sum : ∀ T : J → C, Cofan fun j => replace (T j)
  isColimit : ∀ T : J → C, IsColimit (sum T)
  desc_mem : ∀ (T X : J → C) (s : ∀ j, replace (T j) ⟶ replace (X j)), (∀ j, W (s j)) →
    W (Cofan.IsColimit.desc (isColimit T) fun j => s j ≫ (sum X).inj j)

namespace RightFractionCoproducts

variable {W : MorphismProperty C} {J : Type w} (R : RightFractionCoproducts W J) (L : C ⥤ D)

/-- The image under `L` of a chosen coproduct of replacements. -/
def localizedCofan (T : J → C) : Cofan fun j => L.obj (R.replace (T j)) :=
  Cofan.mk (L.obj (R.sum T).pt) fun j => L.map ((R.sum T).inj j)

@[simp]
theorem localizedCofan_pt (T : J → C) : (R.localizedCofan L T).pt = L.obj (R.sum T).pt := rfl

@[simp]
theorem localizedCofan_inj (T : J → C) (j : J) :
    (R.localizedCofan L T).inj j = L.map ((R.sum T).inj j) := rfl

variable [L.IsLocalization W] [W.HasRightCalculusOfFractions]

/-- Two numerators over a common denominator `t` into the chosen coproduct that agree after
restriction to every summand have the same image under `L`. -/
theorem map_eq_of_denominator (T : J → C) {Z Y : C} (t : Z ⟶ (R.sum T).pt) (ht : W t)
    (b b' : Z ⟶ Y)
    (h : ∀ j, L.map ((R.sum T).inj j) ≫ (Localization.isoOfHom L W t ht).inv ≫ L.map b =
      L.map ((R.sum T).inj j) ≫ (Localization.isoOfHom L W t ht).inv ≫ L.map b') :
    L.map b = L.map b' := by
  have key : ∀ j, ∃ (S : C) (r : S ⟶ R.replace (T j)) (z : S ⟶ Z), W r ∧
      r ≫ (R.sum T).inj j = z ≫ t ∧ z ≫ b = z ≫ b' := by
    intro j
    obtain ⟨ψ, hψ⟩ := (LeftFraction.mk ((R.sum T).inj j) t ht).exists_rightFraction
    have : IsIso (L.map ψ.s) := Localization.inverts L W _ ψ.hs
    have e1 : L.map ((R.sum T).inj j) ≫ (Localization.isoOfHom L W t ht).inv =
        inv (L.map ψ.s) ≫ L.map ψ.f := by
      rw [← cancel_epi (L.map ψ.s), IsIso.hom_inv_id_assoc, ← L.map_comp_assoc]
      have hψ' : ψ.s ≫ (R.sum T).inj j = ψ.f ≫ t := hψ
      rw [hψ', L.map_comp_assoc]
      have : L.map t ≫ (Localization.isoOfHom L W t ht).inv = 𝟙 _ :=
        (Localization.isoOfHom L W t ht).hom_inv_id
      rw [this, Category.comp_id]
    have e2 : L.map (ψ.f ≫ b) = L.map (ψ.f ≫ b') := by
      have hj := h j
      rw [← Category.assoc, e1, ← Category.assoc, e1, Category.assoc, Category.assoc,
        cancel_epi] at hj
      rw [L.map_comp, L.map_comp, hj]
    obtain ⟨S, r, hr, hrb⟩ := (MorphismProperty.map_eq_iff_precomp L W _ _).1 e2
    refine ⟨S, r ≫ ψ.s, r ≫ ψ.f, W.comp_mem _ _ hr ψ.hs, ?_, ?_⟩
    · have hψ' : ψ.s ≫ (R.sum T).inj j = ψ.f ≫ t := hψ
      rw [Category.assoc, hψ', Category.assoc]
    · simpa only [Category.assoc] using hrb
  choose S r z hr hrt hzb using key
  let u : (R.sum S).pt ⟶ Z := Cofan.IsColimit.desc (R.isColimit S) fun j => R.π (S j) ≫ z j
  have hu : u ≫ t = Cofan.IsColimit.desc (R.isColimit S)
      fun j => (R.π (S j) ≫ r j) ≫ (R.sum T).inj j := by
    refine Cofan.IsColimit.hom_ext (R.isColimit S) _ _ fun j => ?_
    rw [Cofan.IsColimit.fac_assoc, Cofan.IsColimit.fac, Category.assoc, Category.assoc, hrt]
  have hW : W (u ≫ t) := by
    rw [hu]
    exact R.desc_mem S T _ fun j => W.comp_mem _ _ (R.π_mem _) (hr j)
  have h1 : IsIso (L.map (u ≫ t)) := Localization.inverts L W _ hW
  have h2 : IsIso (L.map t) := Localization.inverts L W _ ht
  rw [L.map_comp] at h1
  have h3 : IsIso (L.map u) := IsIso.of_isIso_comp_right (L.map u) (L.map t)
  have hub : u ≫ b = u ≫ b' := Cofan.IsColimit.hom_ext (R.isColimit S) _ _ fun j => by
    rw [Cofan.IsColimit.fac_assoc, Cofan.IsColimit.fac_assoc, Category.assoc, Category.assoc,
      hzb]
  rw [← cancel_epi (L.map u), ← L.map_comp, ← L.map_comp, hub]

/-- Morphisms out of the image of a chosen coproduct are determined by their restrictions
to the summands. -/
theorem hom_ext (T : J → C) {Y : D} (m₁ m₂ : L.obj (R.sum T).pt ⟶ Y)
    (h : ∀ j, L.map ((R.sum T).inj j) ≫ m₁ = L.map ((R.sum T).inj j) ≫ m₂) : m₁ = m₂ := by
  have := Localization.essSurj L W
  let e := L.objObjPreimageIso Y
  suffices hs : m₁ ≫ e.inv = m₂ ≫ e.inv by
    rwa [cancel_mono] at hs
  obtain ⟨φ₁, h₁⟩ := Localization.exists_rightFraction L W (m₁ ≫ e.inv)
  obtain ⟨φ₂, h₂⟩ := Localization.exists_rightFraction L W (m₂ ≫ e.inv)
  obtain ⟨ψ, hψ⟩ := (LeftFraction.mk φ₁.s φ₂.s φ₂.hs).exists_rightFraction
  have hψ' : ψ.s ≫ φ₁.s = ψ.f ≫ φ₂.s := hψ
  have ht : W (ψ.s ≫ φ₁.s) := W.comp_mem _ _ ψ.hs φ₁.hs
  have : IsIso (L.map φ₁.s) := Localization.inverts L W _ φ₁.hs
  have : IsIso (L.map φ₂.s) := Localization.inverts L W _ φ₂.hs
  have hA : m₁ ≫ e.inv =
      (Localization.isoOfHom L W _ ht).inv ≫ L.map (ψ.s ≫ φ₁.f) := by
    rw [h₁, ← cancel_epi (Localization.isoOfHom L W _ ht).hom, Iso.hom_inv_id_assoc,
      Localization.isoOfHom_hom, MorphismProperty.RightFraction.map, L.map_comp,
      Category.assoc, IsIso.hom_inv_id_assoc, L.map_comp]
  have hB : m₂ ≫ e.inv =
      (Localization.isoOfHom L W _ ht).inv ≫ L.map (ψ.f ≫ φ₂.f) := by
    rw [h₂, ← cancel_epi (Localization.isoOfHom L W _ ht).hom, Iso.hom_inv_id_assoc,
      Localization.isoOfHom_hom, MorphismProperty.RightFraction.map, hψ', L.map_comp,
      Category.assoc, IsIso.hom_inv_id_assoc, L.map_comp]
  rw [hA, hB, R.map_eq_of_denominator L T _ ht _ _ fun j => ?_]
  rw [← hA, ← hB, ← Category.assoc, h j, Category.assoc]

variable [L.EssSurj]

variable (W) in
/-- A chosen right fraction representing `f` followed by the comparison with the chosen
preimage of its target. -/
def fraction {X : C} {Y : D} (f : L.obj X ⟶ Y) : W.RightFraction X (L.objPreimage Y) :=
  Classical.choose (Localization.exists_rightFraction L W (f ≫ (L.objObjPreimageIso Y).inv))

variable (W) in
theorem fraction_spec {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    f ≫ (L.objObjPreimageIso Y).inv = (fraction W L f).map L (Localization.inverts L W) :=
  Classical.choose_spec (Localization.exists_rightFraction L W (f ≫ (L.objObjPreimageIso Y).inv))

variable {L}

/-- The family of sources of the chosen fractions of a family of morphisms. -/
abbrev descSource (T : J → C) {Y : D} (f : ∀ j, L.obj (R.replace (T j)) ⟶ Y) : J → C :=
  fun j => (fraction W L (f j)).X'

/-- The induced denominator between chosen coproducts. -/
def descDenominator (T : J → C) {Y : D} (f : ∀ j, L.obj (R.replace (T j)) ⟶ Y) :
    (R.sum (R.descSource T f)).pt ⟶ (R.sum T).pt :=
  Cofan.IsColimit.desc (R.isColimit _) fun j =>
    (R.π _ ≫ (fraction W L (f j)).s) ≫ (R.sum T).inj j

theorem descDenominator_mem (T : J → C) {Y : D} (f : ∀ j, L.obj (R.replace (T j)) ⟶ Y) :
    W (R.descDenominator T f) :=
  R.desc_mem _ T _ fun j => W.comp_mem _ _ (R.π_mem _) (fraction W L (f j)).hs

/-- The induced numerator on the chosen coproduct of the sources. -/
def descNumerator (T : J → C) {Y : D} (f : ∀ j, L.obj (R.replace (T j)) ⟶ Y) :
    (R.sum (R.descSource T f)).pt ⟶ L.objPreimage Y :=
  Cofan.IsColimit.desc (R.isColimit _) fun j => R.π _ ≫ (fraction W L (f j)).f

/-- The morphism out of the image of a chosen coproduct induced by a family of morphisms out
of the images of the summands. -/
def localizedDesc (T : J → C) {Y : D} (f : ∀ j, L.obj (R.replace (T j)) ⟶ Y) :
    L.obj (R.sum T).pt ⟶ Y :=
  (Localization.isoOfHom L W _ (R.descDenominator_mem T f)).inv ≫
    L.map (R.descNumerator T f) ≫ (L.objObjPreimageIso Y).hom

@[reassoc (attr := simp)]
theorem inj_localizedDesc (T : J → C) {Y : D} (f : ∀ j, L.obj (R.replace (T j)) ⟶ Y)
    (j : J) : L.map ((R.sum T).inj j) ≫ R.localizedDesc T f = f j := by
  have hs : W (R.π _ ≫ (fraction W L (f j)).s) :=
    W.comp_mem _ _ (R.π_mem _) (fraction W L (f j)).hs
  have : IsIso (L.map (R.π _ ≫ (fraction W L (f j)).s)) := Localization.inverts L W _ hs
  have : IsIso (L.map (fraction W L (f j)).s) :=
    Localization.inverts L W _ (fraction W L (f j)).hs
  have : IsIso (L.map (R.π (R.descSource T f j))) := Localization.inverts L W _ (R.π_mem _)
  have hσ : (R.sum (R.descSource T f)).inj j ≫ R.descDenominator T f =
      (R.π _ ≫ (fraction W L (f j)).s) ≫ (R.sum T).inj j :=
    Cofan.IsColimit.fac _ _ j
  have ha : (R.sum (R.descSource T f)).inj j ≫ R.descNumerator T f =
      R.π _ ≫ (fraction W L (f j)).f :=
    Cofan.IsColimit.fac _ _ j
  have e1 : L.map ((R.sum T).inj j) ≫
      (Localization.isoOfHom L W _ (R.descDenominator_mem T f)).inv =
        inv (L.map (R.π _ ≫ (fraction W L (f j)).s)) ≫
          L.map ((R.sum (R.descSource T f)).inj j) := by
    rw [← cancel_epi (L.map (R.π _ ≫ (fraction W L (f j)).s)), IsIso.hom_inv_id_assoc,
      ← L.map_comp_assoc, ← hσ, L.map_comp_assoc, Localization.isoOfHom_hom_inv_id,
      Category.comp_id]
  have e2 := fraction_spec W L (f j)
  rw [MorphismProperty.RightFraction.map] at e2
  rw [localizedDesc, ← Category.assoc, e1, Category.assoc, ← L.map_comp_assoc, ha]
  simp only [Functor.map_comp, IsIso.inv_comp, Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← Category.assoc, ← e2, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The image under `L` of a chosen coproduct of replacements is a coproduct. -/
def isColimitLocalizedCofan (T : J → C) : IsColimit (R.localizedCofan L T) :=
  Cofan.IsColimit.mk _ (fun s => R.localizedDesc T s.inj)
    (fun s j => R.inj_localizedDesc T s.inj j)
    (fun s m hm => R.hom_ext L T _ _ fun j => by
      rw [R.inj_localizedDesc]
      exact hm j)

variable (L) in
/-- The image under `L` of a chosen coproduct, as a cofan of the images of the original
objects through the inverses of the comparison morphisms. -/
def originalCofan (T : J → C) : Cofan fun j => L.obj (T j) :=
  Cofan.mk (L.obj (R.sum T).pt) fun j =>
    (Localization.isoOfHom L W _ (R.π_mem (T j))).inv ≫ L.map ((R.sum T).inj j)

omit [W.HasRightCalculusOfFractions] [L.EssSurj] in
@[simp]
theorem originalCofan_pt (T : J → C) : (R.originalCofan L T).pt = L.obj (R.sum T).pt := rfl

omit [W.HasRightCalculusOfFractions] [L.EssSurj] in
theorem originalCofan_inj_comp (T : J → C) (j : J) {Z : D} (m : L.obj (R.sum T).pt ⟶ Z) :
    (R.originalCofan L T).inj j ≫ m =
      (Localization.isoOfHom L W _ (R.π_mem (T j))).inv ≫ L.map ((R.sum T).inj j) ≫ m :=
  Category.assoc _ _ _

/-- The image under `L` of a chosen coproduct is a coproduct of the images of the original
objects. -/
def isColimitOriginalCofan (T : J → C) : IsColimit (R.originalCofan L T) :=
  Cofan.IsColimit.mk _ (fun s => R.localizedDesc T fun j => L.map (R.π (T j)) ≫ s.inj j)
    (fun s j => by
      rw [originalCofan_inj_comp, R.inj_localizedDesc, Localization.isoOfHom_inv_hom_id_assoc])
    (fun s m hm => R.hom_ext L T _ _ fun j => by
      rw [R.inj_localizedDesc, ← hm j]
      exact (Localization.isoOfHom_hom_inv_id_assoc (L := L) (W := W) (R.π (T j))
        (R.π_mem (T j)) _).symm.trans
        (congrArg (fun x => L.map (R.π (T j)) ≫ x) (R.originalCofan_inj_comp T j m).symm))

end RightFractionCoproducts

end Langlands.CategoryTheory
