import Langlands.AlgebraicGeometry.RelativeDerivations
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Relative derivations on fibre products

A relative derivation on a fibre product of schemes which kills every section
pulled back along both projections vanishes identically.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

namespace Langlands.Scheme.RelativeDerivation

section Kernel

variable {X S : AlgebraicGeometry.Scheme.{u}} {π : X ⟶ S} {M : X.Modules}

@[simp]
lemma app_one (d : RelativeDerivation π M) (U : X.Opens) : d.app U 1 = 0 :=
  d.d_one (op U)

/-- The sections over an open killed by a relative derivation form a subring. -/
def kerSubring (d : RelativeDerivation π M) (U : X.Opens) : Subring Γ(X, U) where
  carrier := {a | d.app U a = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [app_mul, ha, hb, smul_zero, smul_zero, add_zero]
  one_mem' := app_one d U
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [app_add, ha, hb, add_zero]
  zero_mem' := map_zero (d.app U)
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_neg, ha, neg_zero]

/-- A section is killed by a relative derivation if it is killed locally. -/
lemma app_eq_zero_of_local (d : RelativeDerivation π M) {U : X.Opens} (a : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      d.app V (X.presheaf.map (homOfLE hV).op a) = 0) :
    d.app U a = 0 := by
  refine M.isSheaf.section_ext (U := op U) (s := d.app U a) (t := 0) ?_
  intro x hx
  obtain ⟨V, hV, hxV, hd⟩ := h x hx
  refine ⟨V, hV, hxV, ?_⟩
  rw [← app_restrict, hd, map_zero]

/-- If a relative derivation kills all sections over an affine open, it kills all
sections over each of its basic opens. -/
lemma app_basicOpen_eq_zero (d : RelativeDerivation π M) {U : X.Opens}
    (hU : IsAffineOpen U) (hd : ∀ a : Γ(X, U), d.app U a = 0) (r : Γ(X, U))
    (b : Γ(X, X.basicOpen r)) :
    d.app (X.basicOpen r) b = 0 := by
  have := hU.isLocalization_basicOpen r
  have hres : ∀ c : Γ(X, U),
      d.app (X.basicOpen r) (algebraMap Γ(X, U) Γ(X, X.basicOpen r) c) = 0 := by
    intro c
    change d.app _ (X.presheaf.map (homOfLE (X.basicOpen_le r)).op c) = 0
    rw [app_restrict, hd, map_zero]
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) b
  have h := congrArg (d.app (X.basicOpen r))
    (IsLocalization.mk'_spec Γ(X, X.basicOpen r) a s)
  rw [app_mul, hres, hres, smul_zero, zero_add] at h
  exact (IsLocalization.map_units Γ(X, X.basicOpen r) s).smul_eq_zero.mp h

end Kernel

section Pullback

variable {Y X T B S : AlgebraicGeometry.Scheme.{u}}
  {g : Y ⟶ X} {iY : Y ⟶ T} {iX : X ⟶ B} {f : T ⟶ B}
  {π : Y ⟶ S} {M : Y.Modules}

/-- On the product of affine opens of a pullback square, a relative derivation killing
the sections pulled back along both projections kills every section. -/
lemma app_eq_zero_of_isAffineOpen (H : IsPullback g iY iX f) (d : RelativeDerivation π M)
    (hX : ∀ (U : X.Opens) (a : Γ(X, U)), d.app (g ⁻¹ᵁ U) (g.app U a) = 0)
    (hT : ∀ (U : T.Opens) (a : Γ(T, U)), d.app (iY ⁻¹ᵁ U) (iY.app U a) = 0)
    {UB : B.Opens} {UT : T.Opens} {UX : X.Opens}
    (hUBT : UT ≤ f ⁻¹ᵁ UB) (hUBX : UX ≤ iX ⁻¹ᵁ UB)
    (hUB : IsAffineOpen UB) (hUT : IsAffineOpen UT) (hUX : IsAffineOpen UX)
    (b : Γ(Y, g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)) :
    d.app (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) b = 0 := by
  let K := kerSubring d (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
  have hgX : ∀ a, g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left a ∈ K := by
    intro a
    change d.app _ (Y.presheaf.map (homOfLE inf_le_left).op (g.app UX a)) = 0
    rw [app_restrict, hX, map_zero]
  have hgT : ∀ a, iY.appLE UT (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_right a ∈ K := by
    intro a
    change d.app _ (Y.presheaf.map (homOfLE inf_le_right).op (iY.app UT a)) = 0
    rw [app_restrict, hT, map_zero]
  let φX : Γ(X, UX) ⟶ CommRingCat.of K := CommRingCat.ofHom
    ((g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left).hom.codRestrict K hgX)
  let φT : Γ(T, UT) ⟶ CommRingCat.of K := CommRingCat.ofHom
    ((iY.appLE UT (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_right).hom.codRestrict K hgT)
  have hsq : iX.appLE UB UX hUBX ≫ g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left =
      f.appLE UB UT hUBT ≫ iY.appLE UT (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_right := by
    simp only [Scheme.Hom.appLE_comp_appLE, H.w]
  have hw : iX.appLE UB UX hUBX ≫ φX = f.appLE UB UT hUBT ≫ φT := by
    ext a
    exact ConcreteCategory.congr_hom hsq a
  have hfac : pushout.desc φX φT hw ≫ CommRingCat.ofHom K.subtype =
      pushoutSection H hUBT hUBX rfl := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc_assoc, pushout.inl_desc]
      rfl
    · rw [pushout.inr_desc_assoc, pushout.inr_desc]
      rfl
  have := isIso_pushoutSection_of_isAffineOpen H hUBT hUBX rfl hUB hUT hUX
  have hb : b = pushoutSection H hUBT hUBX rfl (inv (pushoutSection H hUBT hUBX rfl) b) := by
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  have key : ∀ c, pushoutSection H hUBT hUBX rfl c ∈ K := by
    intro c
    rw [← hfac]
    exact (pushout.desc φX φT hw c).2
  rw [hb]
  exact key _

/-- A relative derivation on the source of a pullback square of schemes vanishes if it
kills every section pulled back along either projection. -/
theorem app_eq_zero_of_isPullback (H : IsPullback g iY iX f) (d : RelativeDerivation π M)
    (hX : ∀ (U : X.Opens) (a : Γ(X, U)), d.app (g ⁻¹ᵁ U) (g.app U a) = 0)
    (hT : ∀ (U : T.Opens) (a : Γ(T, U)), d.app (iY ⁻¹ᵁ U) (iY.app U a) = 0)
    (V : Y.Opens) (b : Γ(Y, V)) :
    d.app V b = 0 := by
  apply app_eq_zero_of_local d b
  intro y hy
  obtain ⟨UB, hUB, hyB, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := iX (g y)) trivial
  obtain ⟨UX, hUX, hyX, hUXB⟩ :=
    exists_isAffineOpen_mem_and_subset (U := iX ⁻¹ᵁ UB) (x := g y) hyB
  have hyB' : f (iY y) ∈ UB := by
    rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]
    exact hyB
  obtain ⟨UT, hUT, hyT, hUTB⟩ :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ UB) (x := iY y) hyB'
  have hW : IsAffineOpen (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) := by
    have : IsAffine _ := hUB
    have : IsAffine _ := hUT
    have : IsAffine _ := hUX
    exact .of_isIso (Scheme.Hom.isPullback_resLE H hUTB hUXB rfl).isoPullback.hom
  obtain ⟨r, hrV, hyr⟩ := hW.exists_basicOpen_le (V := V) ⟨y, hy⟩ ⟨hyX, hyT⟩
  exact ⟨Y.basicOpen r, hrV, hyr, app_basicOpen_eq_zero d hW
    (app_eq_zero_of_isAffineOpen H d hX hT hUTB hUXB hUB hUT hUX) r _⟩

end Pullback

end Langlands.Scheme.RelativeDerivation
