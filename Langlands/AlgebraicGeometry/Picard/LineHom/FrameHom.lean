import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame

/-! # Morphisms between module sheaves with frames on a common cover

Let `M` and `N` be sheaves of modules on a scheme `X` with frames `e i` and `f i` on a common
open cover `T`, with transition functions `g` and `h`. Morphisms `M ⟶ N` correspond exactly to
families of functions `a i` on `T i` intertwining the transitions (`IsGaugeFamily g h a`); the
family of `φ` is determined by `φ (e i) = a i • f i`. For an ordered index type it suffices to
check the intertwining relation on pairs `i < j`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.LineHom

open CocycleGluing

section Cocycle

variable {X : Scheme.{u}} {ι : Type u} {T : ι → X.Opens} {g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}

/-- A unit cocycle is trivial on the diagonal. -/
lemma IsCocycle.self_eq_one (hg : IsCocycle g) (i : ι) : (g i i : Γ(X, T i ⊓ T i)) = 1 := by
  have h := cocycle_res g hg i i i (W := T i ⊓ T i) le_rfl le_rfl le_rfl
  simp only [res_self] at h
  simpa using congrArg (fun z ↦ (↑(g i i)⁻¹ : Γ(X, T i ⊓ T i)) * z) h

/-- The transition functions in the two orders are mutually inverse on `T i ⊓ T j`. -/
lemma IsCocycle.mul_swap_eq_one (hg : IsCocycle g) (i j : ι) :
    (g i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE (le_inf inf_le_right inf_le_left : T i ⊓ T j ≤ T j ⊓ T i)).op
          (g j i : Γ(X, T j ⊓ T i)) = 1 := by
  have h := cocycle_res g hg i j i (W := T i ⊓ T j) le_rfl
    (le_inf inf_le_right inf_le_left) (le_inf inf_le_left inf_le_left)
  rw [IsCocycle.self_eq_one hg i, map_one, res_self] at h
  exact h

end Cocycle

section Gauge

variable {X : Scheme.{u}} {ι : Type u} [LinearOrder ι] {T : ι → X.Opens}
  {g h : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}

/-- For cocycles on an ordered index set, the intertwining relation need only be checked on
pairs `i < j`. -/
lemma isGaugeFamily_iff_of_lt (hg : IsCocycle g) (hh : IsCocycle h) (a : ∀ i : ι, Γ(X, T i)) :
    IsGaugeFamily g h a ↔ ∀ i j : ι, i < j →
      X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (a i) *
          (g i j : Γ(X, T i ⊓ T j)) =
        (h i j : Γ(X, T i ⊓ T j)) *
          X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (a j) := by
  refine ⟨fun ha i j _ ↦ ha i j, fun ha i j ↦ ?_⟩
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact ha i j hij
  · rw [IsCocycle.self_eq_one hg, IsCocycle.self_eq_one hh, mul_one, one_mul]
  · have hρ : T i ⊓ T j ≤ T j ⊓ T i := le_inf inf_le_right inf_le_left
    have e1 := congrArg (fun z ↦ X.presheaf.map (homOfLE hρ).op z) (ha j i hij)
    simp only [map_mul, res_res] at e1
    have e2 := IsCocycle.mul_swap_eq_one hg i j
    have e3 := IsCocycle.mul_swap_eq_one hh i j
    linear_combination
      (-((h i j : Γ(X, T i ⊓ T j)) * (g i j : Γ(X, T i ⊓ T j)))) * e1 +
      ((h i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (a j)) * e2 -
      (X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (a i) *
        (g i j : Γ(X, T i ⊓ T j))) * e3

end Gauge

section Hom

variable {X : Scheme.{u}} {ι : Type u} {T : ι → X.Opens} {M N : X.Modules}
  {e : ∀ i, Γ(M, T i)} {f : ∀ i, Γ(N, T i)}
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (T i))
  (hf : ∀ i, Scheme.Modules.IsFrameOn (f i) (T i))
  {g h : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}
  (hge : IsTransition e g) (hhf : IsTransition f h) (hT : (⨆ i, T i) = ⊤)

/-- Morphisms between module sheaves with frames `e` and `f` on a common cover, with transition
functions `g` and `h`, are exactly the families of functions intertwining `g` and `h`. -/
noncomputable def frameHomEquiv :
    (M ⟶ N) ≃ {a : ∀ i, Γ(X, T i) // IsGaugeFamily g h a} where
  toFun φ := ⟨coeff (isCocycle_of_isTransition he hge) (isCocycle_of_isTransition hf hhf)
      ((frameIso he hge hT).inv ≫ φ ≫ (frameIso hf hhf hT).hom),
    isGaugeFamily_coeff _ _ _⟩
  invFun a := (frameIso he hge hT).hom ≫ gaugeHom a.1 a.2 ≫ (frameIso hf hhf hT).inv
  left_inv φ := by
    dsimp only
    rw [← eq_gaugeHom]
    simp
  right_inv a := by
    apply Subtype.ext
    dsimp only
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact coeff_gaugeHom _ _ a.1 a.2

/-- The family of a morphism `φ` satisfies `φ (e i) = a i • f i`. -/
lemma frameHomEquiv_spec (φ : M ⟶ N) (i : ι) :
    φ.app (T i) (e i) = (frameHomEquiv he hf hge hhf hT φ).1 i • f i := by
  have hg := isCocycle_of_isTransition he hge
  have hh := isCocycle_of_isTransition hf hhf
  have key := app_genSec_top hg hh ((frameIso he hge hT).inv ≫ φ ≫ (frameIso hf hhf hT).hom) i
  have hM := frameIso_inv_app_genSec he hge hT hg i (le_refl (T i))
  have hN := frameIso_inv_app_genSec hf hhf hT hh i (le_refl (T i))
  rw [mres_self] at hM hN
  have k2 := congrArg (fun z ↦ (frameIso hf hhf hT).inv.app (T i) z) key
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at k2
  rw [hM, Scheme.Modules.Hom.app_smul, hN] at k2
  have hid : ∀ z, (frameIso hf hhf hT).inv.app (T i) ((frameIso hf hhf hT).hom.app (T i) z) = z :=
    fun z ↦ by
      rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
        Scheme.Modules.Hom.id_app]
      rfl
  exact (hid _).symm.trans k2

/-- The family of a morphism is characterized by the frame relation. -/
lemma frameHomEquiv_apply_eq (φ : M ⟶ N) (a : ∀ i, Γ(X, T i))
    (ha : ∀ i, φ.app (T i) (e i) = a i • f i) :
    (frameHomEquiv he hf hge hhf hT φ).1 = a := by
  funext i
  apply (hf i (le_refl (T i)) (le_refl (T i))).1
  dsimp only
  rw [mres_self, ← frameHomEquiv_spec, ha]

end Hom

end Langlands.AlgebraicGeometry.Picard.LineHom
