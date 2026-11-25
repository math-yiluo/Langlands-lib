/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDescentDataCategory
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic

/-! Auxiliary steps for Stacks Project, Descent, Lemma 0241. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory

private theorem epi_of_fpqc_singleton {U V : Scheme.{u}} (f : U ⟶ V)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage V) : Epi f := by
  have he : EffectiveEpi f := by
    rw [← Sieve.effectiveEpimorphic_singleton,
      Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
    intro Z
    exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck hf)
  exact inferInstance

private theorem epi_pullback_fst {X X' T : Scheme.{u}} (r : X' ⟶ X)
    (hr : Presieve.singleton r ∈ Scheme.fpqcPrecoverage X) (f : T ⟶ X) :
    Epi (pullback.fst f r) := by
  apply epi_of_fpqc_singleton
  rw [← Presieve.ofArrows_pUnit.{0}] at hr ⊢
  exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} ↦ r) hr f
    (fun _ ↦ pullback.fst f r) (fun _ ↦ pullback.snd f r)
    (fun _ ↦ IsPullback.of_hasPullback f r)

private theorem transport_left_congr {S X T : Scheme.{u}} {a : X ⟶ S}
    {V : Over X} (D : Over.DescentDatum a V) (f₀ f₁ k₀ k₁ : T ⟶ X)
    (h : f₀ ≫ a = f₁ ≫ a) (h' : k₀ ≫ a = k₁ ≫ a)
    (z : Over.mk f₀ ⟶ V) (w : Over.mk k₀ ⟶ V)
    (e₀ : f₀ = k₀) (e₁ : f₁ = k₁) (ez : z.left = w.left) :
    (D.transport f₀ f₁ h z).left = (D.transport k₀ k₁ h' w).left := by
  subst k₀
  subst k₁
  have ez' : z = w := by ext; exact ez
  subst w
  rfl

/-- A descended underlying morphism preserves the original descent data.
Source: Stacks Project, Descent, Lemma 0241, verification after refinement.
(blueprint: lem-galois-fpqc-descent-morphism-compatibility).

Proof: The two sides of the compatibility equation are morphisms over X ×_S X.
Pull back along X' ×_S X' → X ×_S X. By the base-change equations for both data
and the reconstruction equation for α, their pullbacks are equal by β.commutes.
Factor the refinement as the two successive base changes of r. Each is fpqc,
so the injectivity part of Tag 02W0, applied twice, reflects this equality.
Evaluate the resulting equation at arbitrary test points to obtain the stated
transport identity. No existence or uniqueness of α is used in this step. -/
theorem fpqc_descent_morphism_compatibility
    {S X X' : Scheme.{u}} (a : X ⟶ S) (r : X' ⟶ X)
    (hr : Presieve.singleton r ∈ Scheme.fpqcPrecoverage X)
    (F : Over.DescentDataCategory a ⥤ Over.DescentDataCategory (r ≫ a))
    (q : ∀ A : Over.DescentDataCategory a, (F.obj A).V.left ⟶ A.V.left)
    (hq : ∀ A, ∃ hq : q A ≫ A.V.hom = (F.obj A).V.hom ≫ r,
      IsPullback (q A) (F.obj A).V.hom A.V.hom r ∧
      Over.DescentDatum.IsBaseChange rfl hq A.datum (F.obj A).datum)
    (A B : Over.DescentDataCategory a) (β : F.obj A ⟶ F.obj B)
    (α : A.V ⟶ B.V) (hα : q A ≫ α.left = β.hom.left ≫ q B) :
    ∀ {T : Scheme.{u}} (f₀ f₁ : T ⟶ X) (h : f₀ ≫ a = f₁ ≫ a)
      (z : Over.mk f₀ ⟶ A.V),
      B.datum.transport f₀ f₁ h (z ≫ α) = A.datum.transport f₀ f₁ h z ≫ α := by
  obtain ⟨hqA, hpA, hbA⟩ := hq A
  obtain ⟨hqB, _, hbB⟩ := hq B
  intro T f₀ f₁ h z
  let P := pullback f₀ r
  let p : P ⟶ T := pullback.fst f₀ r
  let Q := pullback (p ≫ f₁) r
  let t : Q ⟶ P := pullback.fst (p ≫ f₁) r
  let g : Q ⟶ T := t ≫ p
  let x₀ : Q ⟶ X' := t ≫ pullback.snd f₀ r
  let x₁ : Q ⟶ X' := pullback.snd (p ≫ f₁) r
  have hg₀ : g ≫ f₀ = x₀ ≫ r := by simp [g, x₀, p, pullback.condition]
  have hg₁ : g ≫ f₁ = x₁ ≫ r := by
    simpa [g, t, Category.assoc] using pullback.condition (f := p ≫ f₁) (g := r)
  have hx : x₀ ≫ (r ≫ a) = x₁ ≫ (r ≫ a) := by
    rw [← Category.assoc, ← hg₀, Category.assoc, h,
      ← Category.assoc, hg₁, Category.assoc]
  let v : Q ⟶ (F.obj A).V.left := hpA.lift (g ≫ z.left) x₀ (by
    simp only [Category.assoc, Over.w]
    exact hg₀)
  have hvq : v ≫ q A = g ≫ z.left := hpA.lift_fst _ _ _
  have hvx : v ≫ (F.obj A).V.hom = x₀ := hpA.lift_snd _ _ _
  let z' : Over.mk x₀ ⟶ (F.obj A).V := Over.homMk v hvx
  have ha := hbA x₀ x₁ hx z'
  have hb := hbB x₀ x₁ hx (z' ≫ β.hom)
  have hc := congrArg (fun k ↦ k.left ≫ q B) (β.commutes x₀ x₁ hx z')
  have hzA : (Over.homMk (z'.left ≫ q A) (by simp [hqA]) :
      Over.mk (x₀ ≫ r) ⟶ A.V) =
      Over.homMk (g ≫ z.left) (by simp [hg₀]) := by
    ext
    exact hvq
  have hzB : (Over.homMk ((z' ≫ β.hom).left ≫ q B) (by simp [hqB]) :
      Over.mk (x₀ ≫ r) ⟶ B.V) =
      Over.homMk (g ≫ (z ≫ α).left) (by simp [hg₀]) := by
    ext
    change v ≫ β.hom.left ≫ q B = g ≫ z.left ≫ α.left
    rw [← hα, ← Category.assoc, hvq, Category.assoc]
  rw [hzA] at ha
  rw [hzB] at hb
  have hnatA := congrArg (fun k ↦ k.left)
    (A.datum.transport_homMk_comp g f₀ f₁ h z)
  have hnatB := congrArg (fun k ↦ k.left)
    (B.datum.transport_homMk_comp g f₀ f₁ h (z ≫ α))
  simp only [Over.comp_left, Over.homMk_left] at hnatA hnatB
  have he : g ≫ (B.datum.transport f₀ f₁ h (z ≫ α)).left =
      g ≫ (A.datum.transport f₀ f₁ h z).left ≫ α.left := by
    rw [← hnatB]
    conv_rhs => rw [← Category.assoc, ← hnatA]
    have ha' : (A.datum.transport (g ≫ f₀) (g ≫ f₁)
        (by simp only [Category.assoc, h])
        ((Over.homMk g : Over.mk (g ≫ f₀) ⟶ Over.mk f₀) ≫ z)).left =
        ((F.obj A).datum.transport x₀ x₁ hx z').left ≫ q A := by
      exact (transport_left_congr A.datum _ _ _ _ _ _ _ _ hg₀ hg₁ rfl).trans ha
    have hb' : (B.datum.transport (g ≫ f₀) (g ≫ f₁)
        (by simp only [Category.assoc, h])
        ((Over.homMk g : Over.mk (g ≫ f₀) ⟶ Over.mk f₀) ≫ z ≫ α)).left =
        ((F.obj B).datum.transport x₀ x₁ hx (z' ≫ β.hom)).left ≫ q B := by
      exact (transport_left_congr B.datum _ _ _ _ _ _ _ _ hg₀ hg₁ rfl).trans hb
    rw [hb', ha']
    simpa only [Over.comp_left, Category.assoc, hα] using hc
  have : Epi p := epi_pullback_fst r hr f₀
  have : Epi t := epi_pullback_fst r hr (p ≫ f₁)
  apply Over.OverMorphism.ext
  apply (cancel_epi p).mp
  apply (cancel_epi t).mp
  simpa only [g, Category.assoc, Over.comp_left] using he

end CategoryTheory
