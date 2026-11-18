import Langlands.AlgebraicGeometry.FiniteEtale.PointwiseClosedImmersion

/-! # Lifting point characters over separably closed fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {K : Type u} [Field K] [IsSepClosed K]

/-- Morphisms from an étale scheme to the multiplicative group are determined
by rational points over a separably closed field. -/
lemma gm_hom_ext_of_isSepClosed {X : Over (Spec (CommRingCat.of K))} [Etale X.hom]
    {f g : X ⟶ (Gm _).X}
    (h : ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X, a ≫ f = a ≫ g) : f = g := by
  apply (Gm.pointsEquiv _ X).injective
  apply Units.ext
  apply Langlands.AlgebraicGeometry.FiniteEtale.section_ext_of_pointValue_of_isSepClosed
  intro a
  rw [pointValue_pointsEquiv, pointValue_pointsEquiv, h a]

/-- Nonzero prescribed values at the rational points of a finite étale scheme
are realized by an invertible global function. -/
lemma exists_unit_pointValue_of_isSepClosed {X : Over (Spec (CommRingCat.of K))}
    [IsFinite X.hom] [Etale X.hom]
    (c : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) → Kˣ) :
    ∃ u : Γ(X.left, ⊤)ˣ, ∀ a, pointValue a (u : Γ(X.left, ⊤)) = c a := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have := finite_points X
  obtain ⟨s, hs⟩ := exists_section_pointValue (fun a => (c a : K))
  obtain ⟨t, ht⟩ := exists_section_pointValue (fun a => (((c a)⁻¹ : Kˣ) : K))
  have hst : s * t = 1 :=
    Langlands.AlgebraicGeometry.FiniteEtale.section_ext_of_pointValue_of_isSepClosed
      fun a => by rw [map_mul, hs, ht, map_one, Units.mul_inv]
  exact ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, hs⟩

/-- An abstract homomorphism on rational points lifts to an actual morphism
to the multiplicative group respecting multiplication. -/
lemma exists_gm_hom_of_points_of_isSepClosed
    (G : CommGroupScheme (Spec (CommRingCat.of K))) [IsFinite G.X.hom] [Etale G.X.hom]
    (φ : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) →* Kˣ) :
    ∃ f : G.X ⟶ (Gm _).X,
      (∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
        (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (a ≫ f)).val = φ a) ∧
      μ[G.X] ≫ f = (fst G.X G.X ≫ f) * (snd G.X G.X ≫ f) := by
  obtain ⟨u, hu⟩ := exists_unit_pointValue_of_isSepClosed (X := G.X) (fun a => φ a)
  have hf : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of K))))
        (a ≫ (Gm.pointsEquiv _ G.X).symm u)).val = φ a := by
    intro a
    rw [← pointValue_pointsEquiv, MulEquiv.apply_symm_apply, hu]
  refine ⟨(Gm.pointsEquiv _ G.X).symm u, hf, ?_⟩
  have : Etale (G.X ⊗ G.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  apply gm_hom_ext_of_isSepClosed
  intro q
  rw [MonObj.comp_mul]
  apply (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of K))))).injective
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom _ =
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom _
  have hq : q ≫ μ[G.X] = (q ≫ fst G.X G.X) * (q ≫ snd G.X G.X) := by
    rw [Hom.mul_def, lift_comp_fst_snd]
  rw [map_mul, Units.val_mul, map_mul, ← Category.assoc, ← Category.assoc, ← Category.assoc,
    hf, hf, hf, hq, map_mul, Units.val_mul]

end Langlands.GroupScheme.Cartier
