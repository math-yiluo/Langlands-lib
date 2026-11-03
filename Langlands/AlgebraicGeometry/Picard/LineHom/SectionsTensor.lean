import Langlands.AlgebraicGeometry.FiniteLinearEquationsScheme
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage

/-! # Sections of a base change over an affine open as a tensor product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.LineHom

attribute [local instance] FiniteLinearEquations.sectionsAlgebra

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))

/-- Every open subset lies in the preimage of the whole target. The statement keeps the
preimage `f ⁻¹ᵁ ⊤` (rather than `⊤`) in its type, as `Scheme.Hom.appLE` expects. -/
lemma le_preimage_top {X Z : Scheme.{u}} (f : X ⟶ Z) (V : X.Opens) : V ≤ f ⁻¹ᵁ ⊤ :=
  le_top

/-- Equal scheme morphisms induce equal maps on sections. -/
private lemma appLE_eq_of_eq {X Z : Scheme.{u}} {f f' : X ⟶ Z} (h : f = f') (U : Z.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V e' := by
  subst h
  rfl

/-- The two scalar actions agree on sections of the base change over `V`. -/
private lemma scalars_compat (T : Over (Spec (.of R))) (V : Y.Opens) :
    T.hom.appTop ≫ (pullback.fst T.hom p).appLE ⊤ (pullback.snd T.hom p ⁻¹ᵁ V) (le_preimage_top _ _) =
      p.appLE ⊤ V (le_preimage_top _ _) ≫ (pullback.snd T.hom p).app V := by
  have h₁ : T.hom.appTop ≫ (pullback.fst T.hom p).appLE ⊤ (pullback.snd T.hom p ⁻¹ᵁ V) (le_preimage_top _ _) =
      (pullback.fst T.hom p ≫ T.hom).appLE ⊤ (pullback.snd T.hom p ⁻¹ᵁ V) (le_preimage_top _ _) :=
    (Scheme.Hom.comp_appLE _ _ _ _ _).symm
  have h₂ : p.appLE ⊤ V (le_preimage_top _ _) ≫ (pullback.snd T.hom p).app V =
      (pullback.snd T.hom p ≫ p).appLE ⊤ (pullback.snd T.hom p ⁻¹ᵁ V) (le_preimage_top _ _) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rw [h₁, h₂]
  exact appLE_eq_of_eq pullback.condition _ _ _ _

/-- The map sending `x ⊗ b` to the product of the pulled-back sections `x` and `b` on the
preimage of `V` in the base change `T ×_{Spec R} Y`. -/
def sectionsTensorHom (T : Over (Spec (.of R))) (V : Y.Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p V
    Γ(T.left, ⊤) ⊗[R] Γ(Y, V) →+ Γ(pullback T.hom p, pullback.snd T.hom p ⁻¹ᵁ V) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom p V
  TensorProduct.liftAddHom
    ((AddMonoidHom.mul.comp
        ((pullback.fst T.hom p).appLE ⊤ (pullback.snd T.hom p ⁻¹ᵁ V) (le_preimage_top _ _)).hom.toAddMonoidHom).compl₂
      ((pullback.snd T.hom p).app V).hom.toAddMonoidHom)
    (fun r x b ↦ by
      have key : (pullback.fst T.hom p).appLE ⊤ (pullback.snd T.hom p ⁻¹ᵁ V) (le_preimage_top _ _)
            (algebraMap R Γ(T.left, ⊤) r) =
          (pullback.snd T.hom p).app V (algebraMap R Γ(Y, V) r) := by
        change ((Scheme.ΓSpecIso (.of R)).inv ≫ T.hom.appTop ≫
            (pullback.fst T.hom p).appLE ⊤ (pullback.snd T.hom p ⁻¹ᵁ V) (le_preimage_top _ _)) r =
          ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appLE ⊤ V (le_preimage_top _ _) ≫ (pullback.snd T.hom p).app V) r
        rw [scalars_compat]
      simp only [AddMonoidHom.compl₂_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        AddMonoidHom.mul_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
        Algebra.smul_def, map_mul]
      erw [key]
      ring)

@[simp]
lemma sectionsTensorHom_tmul (T : Over (Spec (.of R))) (V : Y.Opens) (x : Γ(T.left, ⊤))
    (b : Γ(Y, V)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p V
    sectionsTensorHom p T V (x ⊗ₜ b) =
      (pullback.fst T.hom p).appLE ⊤ (pullback.snd T.hom p ⁻¹ᵁ V) (le_preimage_top _ _) x *
        (pullback.snd T.hom p).app V b :=
  rfl

/-- The first projection of the base change commutes with the map induced by `g`. -/
private lemma fst_appLE_naturality {T' T : Over (Spec (.of R))} (g : T' ⟶ T) (V : Y.Opens)
    (h : pullback.snd T'.hom p ⁻¹ᵁ V ≤
      ((Over.pullback p).map g).left ⁻¹ᵁ (pullback.snd T.hom p ⁻¹ᵁ V)) :
    (pullback.fst T.hom p).appLE ⊤ (pullback.snd T.hom p ⁻¹ᵁ V) (le_preimage_top _ _) ≫
        ((Over.pullback p).map g).left.appLE (pullback.snd T.hom p ⁻¹ᵁ V)
          (pullback.snd T'.hom p ⁻¹ᵁ V) h =
      g.left.appTop ≫ (pullback.fst T'.hom p).appLE ⊤ (pullback.snd T'.hom p ⁻¹ᵁ V) (le_preimage_top _ _) := by
  rw [Scheme.Hom.appLE_comp_appLE]
  exact (appLE_eq_of_eq (pullback.lift_fst _ _ _) _ _ _ _).trans (Scheme.Hom.comp_appLE _ _ _ _ _)

/-- The second projection of the base change commutes with the map induced by `g`. -/
private lemma snd_app_naturality {T' T : Over (Spec (.of R))} (g : T' ⟶ T) (V : Y.Opens)
    (h : pullback.snd T'.hom p ⁻¹ᵁ V ≤
      ((Over.pullback p).map g).left ⁻¹ᵁ (pullback.snd T.hom p ⁻¹ᵁ V)) :
    (pullback.snd T.hom p).app V ≫
        ((Over.pullback p).map g).left.appLE (pullback.snd T.hom p ⁻¹ᵁ V)
          (pullback.snd T'.hom p ⁻¹ᵁ V) h =
      (pullback.snd T'.hom p).app V := by
  rw [Scheme.Hom.app_eq_appLE (pullback.snd T.hom p), Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.app_eq_appLE (pullback.snd T'.hom p)]
  exact appLE_eq_of_eq (pullback.lift_snd _ _ _) _ _ _ _

lemma sectionsTensorHom_naturality {T' T : Over (Spec (.of R))} (g : T' ⟶ T) (V : Y.Opens)
    (h : pullback.snd T'.hom p ⁻¹ᵁ V ≤
      ((Over.pullback p).map g).left ⁻¹ᵁ (pullback.snd T.hom p ⁻¹ᵁ V))
    (z : letI := Scheme.TwoAffineOpenCover.algebraOfHom p V; Γ(T.left, ⊤) ⊗[R] Γ(Y, V)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p V
    ((Over.pullback p).map g).left.appLE (pullback.snd T.hom p ⁻¹ᵁ V)
        (pullback.snd T'.hom p ⁻¹ᵁ V) h (sectionsTensorHom p T V z) =
      sectionsTensorHom p T' V
        (TensorProduct.map (FiniteLinearEquations.pullSections g).toLinearMap LinearMap.id z) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom p V
  induction z with
  | tmul x b =>
    rw [TensorProduct.map_tmul, sectionsTensorHom_tmul, sectionsTensorHom_tmul, map_mul,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, fst_appLE_naturality,
      snd_app_naturality]
    rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- The algebra structure of `TwoAffineOpenCover.algebraOfHom` on global sections is the
structure `FiniteLinearEquations.sectionsAlgebra`. -/
private lemma algebraOfHom_top_eq (T : Over (Spec (.of R))) :
    Scheme.TwoAffineOpenCover.algebraOfHom T.hom ⊤ = FiniteLinearEquations.sectionsAlgebra T := by
  refine Algebra.algebra_ext _ _ fun r ↦ ?_
  have : T.hom.appLE ⊤ ⊤ le_top = T.hom.appTop := Scheme.Hom.appLE_eq_app T.hom (U := ⊤)
  change (T.hom.appLE ⊤ ⊤ le_top) _ = T.hom.appTop _
  rw [this]

lemma sectionsTensorHom_bijective (T : Over (Spec (.of R))) [IsAffine T.left] {V : Y.Opens}
    (hV : IsAffineOpen V) : Function.Bijective (sectionsTensorHom p T V) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom p V
  let := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst T.hom p ≫ T.hom)
    (pullback.fst T.hom p ⁻¹ᵁ ⊤ ⊓ pullback.snd T.hom p ⁻¹ᵁ V)
  have H := Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
    T.hom p ⊤ (isAffineOpen_top T.left) V hV
  rw [algebraOfHom_top_eq] at H
  obtain ⟨-, e, he⟩ := H
  have hW : pullback.snd T.hom p ⁻¹ᵁ V = pullback.fst T.hom p ⁻¹ᵁ ⊤ ⊓ pullback.snd T.hom p ⁻¹ᵁ V := by
    simp
  let ρ := (pullback T.hom p).presheaf.map (eqToHom hW).op
  have hρ : Function.Bijective ρ := ConcreteCategory.bijective_of_isIso ρ
  have hfac : ∀ z, sectionsTensorHom p T V z = ρ (e z) := by
    intro z
    induction z with
    | tmul x b =>
      rw [he, map_mul, sectionsTensorHom_tmul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
        Scheme.Hom.appLE_map, Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE]
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have : ⇑(sectionsTensorHom p T V) = ρ ∘ e := funext hfac
  rw [this]
  exact hρ.comp e.bijective

end Langlands.AlgebraicGeometry.Picard.LineHom
