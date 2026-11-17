import Langlands.Algebra.SmoothNilIdealLifting
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Sections of smooth schemes over local nil thickenings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SmoothNilIdealSections

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
  {X : Scheme.{u}}

/-- A point over `C` lifts to a section over `R`. -/
def SectionLiftingProperty (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∀ s : Spec (CommRingCat.of C) ⟶ X,
    s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)) →
      ∃ t : Spec (CommRingCat.of R) ⟶ X,
        t ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ t = s

/-- A smooth scheme lifts points over a local quotient through an arbitrary nil
kernel. No nilpotence bound on the whole kernel is required. -/
theorem exists_lift_of_nil_kernel [IsLocalRing C]
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (hq : Function.Surjective (algebraMap R C))
    (hnil : RingHom.ker (algebraMap R C) ≤ nilradical R)
    (s : Spec (CommRingCat.of C) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    ∃ t : Spec (CommRingCat.of R) ⟶ X,
      t ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ t = s := by
  classical
  let x := s (IsLocalRing.closedPoint C)
  let U := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hxU : s (IsLocalRing.closedPoint C) ∈ U := X.affineCover.covers x
  have hrange : Set.range s ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ s ⁻¹ᵁ U := by
      rw [Scheme.preimage_eq_top_of_closedPoint_mem s hxU]
      trivial
    exact hz
  let s' := IsOpenImmersion.lift hU.fromSpec s hrange
  have hs' : s' ≫ hU.fromSpec = s := IsOpenImmersion.lift_fac ..
  let A : CommRingCat := Γ(X, U)
  let α : CommRingCat.of R ⟶ A := Spec.preimage (hU.fromSpec ≫ f)
  have hα : Spec.map α = hU.fromSpec ≫ f := Spec.map_preimage _
  let : Algebra R A := α.hom.toAlgebra
  have hsm : Smooth (Spec.map α) := by
    rw [hα]
    infer_instance
  have : Algebra.Smooth R A :=
    RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm)
  let γ : A ⟶ CommRingCat.of C := Spec.preimage s'
  have hγ : α ≫ γ = CommRingCat.ofHom (algebraMap R C) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, hα, ← Category.assoc, hs', hs]
  let ψ : A →ₐ[R] C :=
    ⟨γ.hom, fun r => congrArg (fun a : CommRingCat.of R ⟶ CommRingCat.of C => a r) hγ⟩
  obtain ⟨l, hl⟩ := Langlands.SmoothNilIdealLifting.exists_lift_of_nil_kernel
    ψ (Algebra.ofId R C) hq hnil
  refine ⟨Spec.map (CommRingCat.ofHom l.toRingHom) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp]
    have he : α ≫ CommRingCat.ofHom l.toRingHom = 𝟙 _ := by
      ext r
      exact l.commutes r
    rw [he, Spec.map_id]
  · rw [← Spec.map_comp_assoc]
    have he : CommRingCat.ofHom l.toRingHom ≫
        CommRingCat.ofHom (algebraMap R C) = γ := by
      ext a
      exact AlgHom.congr_fun hl a
    rw [he, Spec.map_preimage, hs']

/-- The quotient version for every nil ideal in a local ring. -/
theorem exists_lift_of_nil_ideal [IsLocalRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (I : Ideal R) (hI : I ≤ nilradical R)
    (s : Spec (CommRingCat.of (R ⧸ I)) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ∃ t : Spec (CommRingCat.of R) ⟶ X,
      t ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t = s := by
  have hIne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ nilradical R := hI (by simp [h])
    exact not_isNilpotent_one (mem_nilradical.mp h1)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  apply exists_lift_of_nil_kernel f Ideal.Quotient.mk_surjective _ s hs
  simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using hI

end Langlands.AlgebraicGeometry.SmoothNilIdealSections
