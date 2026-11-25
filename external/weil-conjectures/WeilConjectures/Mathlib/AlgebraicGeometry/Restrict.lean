/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Restrictions of morphisms of schemes along open immersions

We record:

- `AlgebraicGeometry.morphismRestrictArrowIso` — transport of a morphism restriction along
  compatible open immersions;
- `AlgebraicGeometry.mem_opensRange_homOfLE` / `AlgebraicGeometry.homOfLE_preimage_opensRange`
  — membership and preimage formulas for the ranges of inclusions of opens;
- `AlgebraicGeometry.Scheme.basicOpenUnit` — a global section `b`, as a unit on the basic open
  `X_b`;
- `AlgebraicGeometry.Scheme.divBasicOpen` — the quotient `a / b` of two global sections, as a
  section over the basic open `X_b`, where `b` is invertible.

- `AlgebraicGeometry.isPullback_resLE_homOfLE` — the restriction of a morphism to a smaller open
  of the target is the base change of its restriction to a larger one;
- `AlgebraicGeometry.Scheme.Hom.surjective_resLE_appTop` — surjectivity of `appLE` implies
  surjectivity of the induced map on global sections of the restrictions;
- `AlgebraicGeometry.exists_opens_restrict_preimage` — a morphism defined on an open subscheme
  restricts to the open subscheme of points mapping into a given open of the target;
- `AlgebraicGeometry.Scheme.Opens.isIso_ι_of_eq_top` — the inclusion of the open `⊤` is an
  isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y Z Z' : Scheme.{u}}

/-- If `e ≫ f = q ≫ j` with `e`, `j` open immersions and `f ⁻¹ᵁ (range j) = range e`, then
the restriction `f ∣_ j.opensRange` is isomorphic to `q` in the arrow category. -/
noncomputable def morphismRestrictArrowIso (f : X ⟶ Y) {e : Z ⟶ X} {j : Z' ⟶ Y}
    (q : Z ⟶ Z') [IsOpenImmersion e] [IsOpenImmersion j]
    (w : e ≫ f = q ≫ j) (h : f ⁻¹ᵁ j.opensRange = e.opensRange) :
    Arrow.mk (f ∣_ j.opensRange) ≅ Arrow.mk q := by
  have hα : Set.range ⇑(f ⁻¹ᵁ j.opensRange).ι = Set.range ⇑e := by
    rw [Scheme.Opens.range_ι, h]; rfl
  have hβ : Set.range ⇑j.opensRange.ι = Set.range ⇑j := by
    rw [Scheme.Opens.range_ι]; rfl
  refine Arrow.isoMk' (f ∣_ j.opensRange) q
    (IsOpenImmersion.isoOfRangeEq (f ⁻¹ᵁ j.opensRange).ι e hα)
    (IsOpenImmersion.isoOfRangeEq j.opensRange.ι j hβ) ?_
  rw [← cancel_mono j, Category.assoc, Category.assoc, ← w,
    IsOpenImmersion.isoOfRangeEq_hom_fac_assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, morphismRestrict_ι]

/-- An open immersion with image `U` has the same range as the inclusion of `U`. -/
lemma Scheme.Hom.range_eq_range_ι_of_opensRange_eq (f : X ⟶ Y) [IsOpenImmersion f] {U : Y.Opens}
    (h : f.opensRange = U) : Set.range f = Set.range U.ι :=
  (coe_opensRange f).symm.trans ((congrArg SetLike.coe h).trans (Scheme.Opens.range_ι U).symm)

/-- Membership in the range of the inclusion of a smaller open. -/
lemma mem_opensRange_homOfLE {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V)
    (x : V.toScheme) : x ∈ (X.homOfLE hUV).opensRange ↔ x.1 ∈ U := by
  rw [Scheme.opensRange_homOfLE]
  exact Iff.rfl

/-- Preimages of ranges of inclusions of opens. -/
lemma homOfLE_preimage_opensRange {X : Scheme.{u}} {U V W : X.Opens} (hWU : W ≤ U)
    (hUV : U ≤ V) :
    X.homOfLE hUV ⁻¹ᵁ (X.homOfLE (hWU.trans hUV)).opensRange =
      (X.homOfLE hWU).opensRange := by
  rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage,
    Scheme.homOfLE_ι]

section BasicOpen

variable (X : Scheme.{u})

/-- The restriction of a global section `b` to the basic open `X_b` is a unit. -/
lemma Scheme.isUnit_ι_appTop_basicOpen (b : Γ(X, ⊤)) :
    IsUnit ((X.basicOpen b).ι.appTop b) := by
  refine Scheme.isUnit_of_basicOpen_eq_top _ ?_
  rw [← Scheme.preimage_basicOpen_top, Scheme.Opens.ι_preimage_self]

/-- A global section `b`, restricted to the basic open `X_b`, as a unit there. -/
noncomputable def Scheme.basicOpenUnit (b : Γ(X, ⊤)) : Γ((X.basicOpen b : Scheme.{u}), ⊤)ˣ :=
  (X.isUnit_ι_appTop_basicOpen b).unit

/-- The quotient `a / b` of two global sections of `X`, as a section over the basic open
`X_b`, where `b` becomes invertible. -/
noncomputable def Scheme.divBasicOpen (a b : Γ(X, ⊤)) : Γ((X.basicOpen b : Scheme.{u}), ⊤) :=
  Ring.inverse ((X.basicOpen b).ι.appTop b) * (X.basicOpen b).ι.appTop a

@[simp]
lemma Scheme.divBasicOpen_mul_self (a b : Γ(X, ⊤)) :
    X.divBasicOpen a b * (X.basicOpen b).ι.appTop b = (X.basicOpen b).ι.appTop a := by
  rw [Scheme.divBasicOpen, mul_right_comm,
    Ring.inverse_mul_cancel _ (X.isUnit_ι_appTop_basicOpen b), one_mul]

/-- `a / b` is the unique section over `X_b` whose product with `b` is `a`. -/
lemma Scheme.eq_divBasicOpen {a b : Γ(X, ⊤)} {v : Γ((X.basicOpen b : Scheme.{u}), ⊤)}
    (h : v * (X.basicOpen b).ι.appTop b = (X.basicOpen b).ι.appTop a) :
    v = X.divBasicOpen a b :=
  (X.isUnit_ι_appTop_basicOpen b).mul_right_cancel (h.trans (X.divBasicOpen_mul_self a b).symm)

end BasicOpen

open CategoryTheory.Limits in
/-- The restriction of `f : X ⟶ Y` to an open `W` of `Y` is the base change of its restriction
to a larger open `U`, provided that the chosen open `W'` of `X` is the intersection of `U'` with
the preimage of `W`. -/
lemma isPullback_resLE_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U W : Y.Opens} (h : W ≤ U)
    {U' W' : X.Opens} (h' : W' ≤ U') (e : U' ≤ f ⁻¹ᵁ U) (e' : W' ≤ f ⁻¹ᵁ W)
    (hpb : U' ⊓ f ⁻¹ᵁ W ≤ W') :
    IsPullback (f.resLE W W' e') (X.homOfLE h') (Y.homOfLE h) (f.resLE U U' e) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [← cancel_mono U.ι]
    simp [Scheme.Hom.resLE_comp_ι]
  · rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage]
    refine le_antisymm (fun x hx ↦ hpb ⟨x.2, hx⟩) (fun x hx ↦ e' hx)

/-- If `f.appLE U V e` is surjective, so is the map induced by the restriction `f.resLE U V e`
on global sections. -/
lemma Scheme.Hom.surjective_resLE_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : Function.Surjective (f.appLE U V e)) :
    Function.Surjective ((f.resLE U V e).appTop) := by
  intro z
  obtain ⟨y, hy⟩ := h (V.topIso.hom z)
  refine ⟨U.topIso.inv y, ?_⟩
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply U.topIso.inv, Iso.inv_hom_id, CommRingCat.id_apply, hy,
    ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

/-- **Restricting a morphism defined on an open subscheme to the preimage of an open of the
target.** For `F : W₁ ⟶ Z` with `W₁` an open subscheme of `X` and `V` an open of `Z`, the set
of points of `W₁` mapping into `V` is an open `W ≤ W₁` of `X`, and `F` restricts to a morphism
`W ⟶ V`. -/
lemma exists_opens_restrict_preimage {X Z : Scheme.{u}} (W₁ : X.Opens)
    (F : W₁.toScheme ⟶ Z) (V : Z.Opens) :
    ∃ (W : X.Opens) (hW : W ≤ W₁) (F' : W.toScheme ⟶ V.toScheme),
      F' ≫ V.ι = X.homOfLE hW ≫ F ∧ ∀ x : W₁.toScheme, x.1 ∈ W ↔ F x ∈ V := by
  have hle : W₁.ι ''ᵁ (F ⁻¹ᵁ V) ≤ W₁ := W₁.ι_image_le _
  have hsub : Set.range (W₁.ι ''ᵁ (F ⁻¹ᵁ V)).ι.base ⊆
      Set.range ((F ⁻¹ᵁ V).ι ≫ W₁.ι).base := by
    simp [Scheme.Opens.range_ι, Set.range_comp]
  set e := IsOpenImmersion.lift ((F ⁻¹ᵁ V).ι ≫ W₁.ι) (W₁.ι ''ᵁ (F ⁻¹ᵁ V)).ι hsub with he
  have hefac : e ≫ ((F ⁻¹ᵁ V).ι ≫ W₁.ι) = (W₁.ι ''ᵁ (F ⁻¹ᵁ V)).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have hhom : X.homOfLE hle = e ≫ (F ⁻¹ᵁ V).ι := by
    rw [← cancel_mono W₁.ι, Scheme.homOfLE_ι, Category.assoc, hefac]
  refine ⟨W₁.ι ''ᵁ (F ⁻¹ᵁ V), hle, e ≫ (F ∣_ V), ?_, ?_⟩
  · rw [hhom, Category.assoc, Category.assoc, morphismRestrict_ι]
  · intro x
    exact Scheme.Opens.mem_ι_image_iff W₁

/-- The inclusion of an open subscheme which is all of `X` is an isomorphism. -/
lemma Scheme.Opens.isIso_ι_of_eq_top {U : X.Opens} (h : U = ⊤) : IsIso U.ι := by
  subst h
  exact ⟨⟨X.topIso.inv, X.ι_toIso_inv, X.toIso_inv_ι⟩⟩

/-- Restricting the global section of `V` attached to `x` along `U ≤ V`. -/
lemma Scheme.homOfLE_appTop_topIso_inv {X : Scheme.{u}} {U V : X.Opens} (e : U ≤ V)
    (x : Γ(X, V)) : (X.homOfLE e).appTop (V.topIso.inv x) =
      U.topIso.inv (X.presheaf.map (homOfLE e).op x) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  change (X.presheaf.map _ ≫ X.presheaf.map _) x = (X.presheaf.map _ ≫ X.presheaf.map _) x
  rw [← Functor.map_comp]
  erw [← Functor.map_comp]
  rfl

/-- Composition of restriction maps. -/
lemma Scheme.presheaf_map_map {X : Scheme.{u}} {U V W : X.Opens} (e₁ : V ≤ U) (e₂ : W ≤ V)
    (x : Γ(X, U)) : X.presheaf.map (homOfLE e₂).op (X.presheaf.map (homOfLE e₁).op x) =
      X.presheaf.map (homOfLE (e₂.trans e₁)).op x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- A section is a unit on any open contained in its basic open. -/
lemma Scheme.isUnit_map_of_le_basicOpen {X : Scheme.{u}} {U V : X.Opens} (f : Γ(X, U))
    (h : V ≤ X.basicOpen f) :
    IsUnit (X.presheaf.map (homOfLE (h.trans (X.basicOpen_le f))).op f) := by
  have := (RingedSpace.isUnit_res_basicOpen X.toRingedSpace f).map
    (X.presheaf.map (homOfLE h).op).hom
  exact (X.presheaf_map_map (X.basicOpen_le f) h f) ▸ this

/-- Restriction along an equality of opens is injective. -/
lemma Scheme.eq_of_map_eq_of_eq {X : Scheme.{u}} {U V : X.Opens} (e : V = U) {x y : Γ(X, U)}
    (h : X.presheaf.map (homOfLE e.le).op x = X.presheaf.map (homOfLE e.le).op y) : x = y := by
  subst e
  simpa using h

end AlgebraicGeometry
