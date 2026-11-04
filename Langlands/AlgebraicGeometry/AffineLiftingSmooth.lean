import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.RingHom.Smooth

/-! # Smoothness of morphisms of affine schemes by infinitesimal lifting

A locally finitely presented morphism `f : X ⟶ Y` of affine schemes over `Spec R` is smooth
when every square-zero lifting problem against the spectrum of an `R`-algebra has a solution.
This is the infinitesimal lifting criterion, phrased with test spectra over `Spec R`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLifting

variable {R : CommRingCat.{u}}

/-- Lifting along square-zero quotients of `R`-algebras, compatibly with a map `φ : B ⟶ A`,
makes `A` formally smooth over `B`. -/
theorem formallySmooth_of_lifting {A B : CommAlgCat.{u} R} (φ : B ⟶ A)
    (H : ∀ (C : CommAlgCat.{u} R) (I : Ideal C), I ^ 2 = ⊥ → ∀ (y : B ⟶ C)
      (x₀ : A ⟶ CommAlgCat.of R (C ⧸ I)),
      φ ≫ x₀ = y ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I) →
      ∃ x : A ⟶ C, φ ≫ x = y ∧ x ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I) = x₀) :
    RingHom.FormallySmooth φ.hom.toRingHom := by
  let : Algebra B A := φ.hom.toRingHom.toAlgebra
  have : IsScalarTower R B A := IsScalarTower.of_algHom φ.hom
  change Algebra.FormallySmooth B A
  refine Algebra.FormallySmooth.of_comp_surjective fun E _ _ I hI ψ => ?_
  algebraize [(algebraMap B E).comp (algebraMap R B)]
  let C : CommAlgCat.{u} R := CommAlgCat.of R E
  let y : B ⟶ C := CommAlgCat.ofHom (IsScalarTower.toAlgHom R B E)
  let x₀ : A ⟶ CommAlgCat.of R (C ⧸ I) := CommAlgCat.ofHom (ψ.restrictScalars R)
  have hx₀ : φ ≫ x₀ = y ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I) := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro b
    exact ψ.commutes b
  obtain ⟨x, hxy, hxred⟩ := H C I hI y x₀ hx₀
  refine ⟨{ x.hom.toRingHom with commutes' := fun b => ?_ }, ?_⟩
  · exact congrArg (fun g => g.hom b) hxy
  · ext a
    exact congrArg (fun g => g.hom a) hxred

/-- **Infinitesimal lifting criterion.** A locally finitely presented morphism of affine
schemes over `Spec R` is smooth when every square-zero lifting problem whose test is the
spectrum of an `R`-algebra has a solution. -/
theorem smooth_of_lifting {X Y : Over (Spec R)} [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f.left]
    (H : ∀ (C : CommAlgCat.{u} R) (I : Ideal C), I ^ 2 = ⊥ →
      ∀ (y : (algSpec R).obj (op C) ⟶ Y)
        (x₀ : (algSpec R).obj (op (CommAlgCat.of R (C ⧸ I))) ⟶ X),
        x₀ ≫ f = (algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)).op ≫ y →
        ∃ x : (algSpec R).obj (op C) ⟶ X, x ≫ f = y ∧
          (algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)).op ≫ x = x₀) :
    Smooth f.left := by
  let hX : (algSpec R).essImage X := essImage_algSpec.mpr inferInstance
  let hY : (algSpec R).essImage Y := essImage_algSpec.mpr inferInstance
  let A : CommAlgCat R := hX.witness.unop
  let B : CommAlgCat R := hY.witness.unop
  let eX : (algSpec R).obj (op A) ≅ X := hX.getIso
  let eY : (algSpec R).obj (op B) ≅ Y := hY.getIso
  let φ : B ⟶ A := (algSpec.fullyFaithful.preimage (eX.hom ≫ f ≫ eY.inv)).unop
  have hφ : (algSpec R).map φ.op = eX.hom ≫ f ≫ eY.inv :=
    algSpec.fullyFaithful.map_preimage _
  have hfs : RingHom.FormallySmooth φ.hom.toRingHom := by
    apply formallySmooth_of_lifting
    intro C I hI y x₀ hx₀
    have hsq : ((algSpec R).map x₀.op ≫ eX.hom) ≫ f =
        (algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)).op ≫
          ((algSpec R).map y.op ≫ eY.hom) := by
      have h := congrArg (fun g => (algSpec R).map g.op ≫ eY.hom) hx₀
      simp only [op_comp, Functor.map_comp, Category.assoc, hφ, Iso.inv_hom_id,
        Category.comp_id] at h
      simpa only [Category.assoc] using h
    obtain ⟨x, hxy, hxred⟩ := H C I hI _ _ hsq
    refine ⟨(algSpec.fullyFaithful.preimage (x ≫ eX.inv)).unop, ?_, ?_⟩
    · apply Quiver.Hom.op_inj
      apply (algSpec R).map_injective
      rw [op_comp, Functor.map_comp, Quiver.Hom.op_unop, algSpec.fullyFaithful.map_preimage,
        hφ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hxy, Iso.hom_inv_id,
        Category.comp_id]
    · apply Quiver.Hom.op_inj
      apply (algSpec R).map_injective
      rw [op_comp, Functor.map_comp, Quiver.Hom.op_unop, algSpec.fullyFaithful.map_preimage,
        ← Category.assoc, hxred, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsIso eX.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eX.hom))
  have : IsIso eX.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eX.inv))
  have : IsIso eY.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eY.hom))
  have : IsIso eY.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eY.inv))
  have hφl : ((algSpec R).map φ.op).left = eX.hom.left ≫ f.left ≫ eY.inv.left := by
    rw [hφ, Over.comp_left, Over.comp_left]
  have : LocallyOfFinitePresentation ((algSpec R).map φ.op).left := by
    rw [hφl]
    infer_instance
  have hfp : RingHom.FinitePresentation φ.hom.toRingHom := by
    have h : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom φ.hom.toRingHom)) :=
      ‹LocallyOfFinitePresentation ((algSpec R).map φ.op).left›
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp h
  have hsm : Smooth ((algSpec R).map φ.op).left := by
    change Smooth (Spec.map (CommRingCat.ofHom φ.hom.toRingHom))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_def.mpr ⟨hfs, hfp⟩)
  have hf₀ : f = eX.inv ≫ (algSpec R).map φ.op ≫ eY.hom := by
    rw [hφ]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have hf : f.left = eX.inv.left ≫ ((algSpec R).map φ.op).left ≫ eY.hom.left := by
    conv_lhs => rw [hf₀]
    rw [Over.comp_left, Over.comp_left]
  rw [hf]
  infer_instance

end Langlands.AlgebraicGeometry.AffineLifting
