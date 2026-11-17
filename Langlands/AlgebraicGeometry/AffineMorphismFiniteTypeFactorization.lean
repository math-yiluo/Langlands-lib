import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Finite-type factorization of morphisms from affine schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry.SubalgebraStages

set_option backward.isDefEq.respectTransparency false in
/-- A morphism from an arbitrary affine scheme into a scheme locally of
finite presentation descends to a finitely generated subalgebra containing
any prescribed finite subset. -/
theorem exists_fg_subalgebra_morphism_factorization
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation p]
    (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))) (s : Finset A) :
    ∃ T : Subalgebra R A, T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ g : Spec (CommRingCat.of T) ⟶ X,
        Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ g = f ∧
        g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  classical
  let I : Type u := {T : Subalgebra R A // T.FG ∧ (↑s : Set A) ⊆ T}
  have : Nonempty I :=
    ⟨⟨Algebra.adjoin R ↑s, Subalgebra.fg_adjoin_finset s, Algebra.subset_adjoin⟩⟩
  have : IsDirected I (· ≤ ·) := ⟨fun T₁ T₂ ↦
    ⟨⟨T₁.1 ⊔ T₂.1, T₁.2.1.sup T₂.2.1,
      T₁.2.2.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩,
      (le_sup_left : T₁.1 ≤ T₁.1 ⊔ T₂.1),
      (le_sup_right : T₂.1 ≤ T₁.1 ⊔ T₂.1)⟩⟩
  let S : I →o Subalgebra R A := ⟨fun T ↦ T.1, fun _ _ h ↦ h⟩
  have hS : ∀ a : A, ∃ i, a ∈ S i := fun a ↦
    ⟨⟨Algebra.adjoin R ↑(insert a s), Subalgebra.fg_adjoin_finset _,
      fun y hy ↦ Algebra.subset_adjoin (by simp [hy])⟩,
      Algebra.subset_adjoin (by simp)⟩
  obtain ⟨hc⟩ :=
    P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC.nonempty_isLimit_specCone
      S hS
  let t : specDiagram S ⟶ (Functor.const Iᵒᵖ).obj (Spec (CommRingCat.of R)) :=
    { app i := specHom S i.unop
      naturality i j h := by simp }
  have (i : Iᵒᵖ) : CompactSpace ((specDiagram S).obj i) := inferInstance
  have (i : Iᵒᵖ) : QuasiSeparatedSpace ((specDiagram S).obj i) := inferInstance
  have {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom ((specDiagram S).map a) := by
    dsimp [specDiagram, specTrans]
    infer_instance
  obtain ⟨i, g, hg, hgp⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (specDiagram S) t p (specCone S) hc f (by
      ext i
      change specLeg S i.unop ≫ specHom S i.unop = f ≫ p
      rw [specLeg_specHom, hf])
  exact ⟨S i.unop, i.unop.2.1, i.unop.2.2, g, hg, hgp⟩

/-- Actual finite-type affine factorization data over the original base. -/
structure FiniteTypeAffineFactorization
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    (f : Spec (CommRingCat.of A) ⟶ X) (s : Finset A) where
  subalgebra : Subalgebra R A
  fg : subalgebra.FG
  contains : (↑s : Set A) ⊆ subalgebra
  hom : Spec (CommRingCat.of subalgebra) ⟶ X
  factorization : Spec.map (CommRingCat.ofHom subalgebra.val.toRingHom) ≫ hom = f
  over_base : hom ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R subalgebra))

/-- Choose a finite-type affine factorization, retaining all equations and
the prescribed finite subset in the resulting data. -/
def finiteTypeAffineFactorization
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation p]
    (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))) (s : Finset A) :
    FiniteTypeAffineFactorization p f s := by
  apply Classical.choice
  obtain ⟨T, hT, hs, g, hg, hgp⟩ :=
    exists_fg_subalgebra_morphism_factorization p f hf s
  exact ⟨⟨T, hT, hs, g, hg, hgp⟩⟩

end Langlands.AlgebraicGeometry
