import Langlands.GroupScheme.Chevalley.IdealCriterion
import Langlands.GroupScheme.AffineLinearEmbedding.Coordinate
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.SubgroupFunctor
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic

/-! # Coordinate restriction and subgroup factorization on every scheme test -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding
open Algebra.TensorProduct (includeLeft includeRight)

variable {R : CommRingCat.{u}}
  {F H : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B C : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (d : (H ⋙ forget GrpCat).CorepresentableBy C)
  (α : H ⟶ F)

/-- The coordinate restriction classifies the image of the universal subgroup point. -/
def coordinateRestriction : B →ₐ[R] C :=
  (e.homEquiv.symm (α.app C (d.homEquiv (𝟙 C)))).hom

theorem pt_coordinateRestriction :
    pt e (A := C) (coordinateRestriction e d α) =
      α.app C (pt d (A := C) (AlgHom.id R C)) := by
  exact pt_homEquiv_symm e _

/-- Restricting coordinates corresponds to the given transformation on all algebra points. -/
theorem pt_comp_coordinateRestriction {A : CommAlgCat.{u} R} (ψ : C →ₐ[R] A) :
    pt e (A := A) (ψ.comp (coordinateRestriction e d α)) =
      α.app A (pt d (A := A) ψ) := by
  rw [pt_comp e (A := C), pt_coordinateRestriction]
  have hn := ConcreteCategory.congr_hom (α.naturality (CommAlgCat.ofHom ψ))
    (pt d (A := C) (AlgHom.id R C))
  change α.app A (H.map (CommAlgCat.ofHom ψ) (pt d (A := C) (AlgHom.id R C))) =
    F.map (CommAlgCat.ofHom ψ) (α.app C (pt d (A := C) (AlgHom.id R C))) at hn
  erw [← hn]
  rw [← pt_comp d (A := C)]
  simp

theorem coordinateRestriction_counit :
    (counit d).comp (coordinateRestriction e d α) = counit e := by
  apply pt_injective e (A := CommAlgCat.of R R)
  rw [pt_comp_coordinateRestriction]
  simp only [counit, pt_homEquiv_symm, map_one]

theorem coordinateRestriction_comul :
    (Algebra.TensorProduct.map (coordinateRestriction e d α)
        (coordinateRestriction e d α)).comp (comul e) =
      (comul d).comp (coordinateRestriction e d α) := by
  apply pt_injective e (A := CommAlgCat.of R (C ⊗[R] C))
  rw [pt_comp_comul e _
      (f := includeLeft.comp (coordinateRestriction e d α))
      (g := includeRight.comp (coordinateRestriction e d α))
      (AlgHom.ext fun b => by simp)
      (AlgHom.ext fun b => by simp),
    pt_comp_coordinateRestriction, pt_comp_coordinateRestriction,
    pt_comp_coordinateRestriction, pt_comul, map_mul]

/-- Coordinate restriction is a homomorphism of the actual coordinate bialgebras. -/
def coordinateRestrictionBialgHom :
    letI := bialgebra e
    letI := bialgebra d
    B →ₐc[R] C := by
  letI := bialgebra e
  letI := bialgebra d
  exact BialgHom.ofAlgHom (coordinateRestriction e d α)
    (coordinateRestriction_counit e d α) (coordinateRestriction_comul e d α)

/-- An algebra point factors through coordinate restriction exactly when its classified
group point lies in the image of the natural homomorphism. -/
theorem factors_coordinateRestriction_iff {A : CommAlgCat.{u} R} (f : B →ₐ[R] A) :
    (∃ ψ : C →ₐ[R] A, ψ.comp (coordinateRestriction e d α) = f) ↔
      ∃ h : H.obj A, α.app A h = pt e f := by
  constructor
  · rintro ⟨ψ, rfl⟩
    exact ⟨pt d ψ, (pt_comp_coordinateRestriction e d α ψ).symm⟩
  · rintro ⟨h, hh⟩
    refine ⟨(d.homEquiv.symm h).hom, ?_⟩
    apply pt_injective e
    rw [pt_comp_coordinateRestriction, pt_homEquiv_symm, hh]

/-- Factorization through the coordinate restriction detects the actual range of the
induced group-scheme map on every scheme test, via its relative global sections. -/
theorem mem_range_iff_coordinate_factors
    (T : Over (Spec R)) (x : T ⟶ (Corepresented.groupScheme F e).X) :
    x ∈ (SubgroupFunctor.range (Corepresented.groupSchemeMap d e α)).carrier T ↔
      ∃ ψ : C →ₐ[R] ((algΓ R).obj T).unop,
        ψ.comp (coordinateRestriction e d α) =
          (e.homEquiv.symm (Corepresented.pointsEquiv F e T x)).hom := by
  rw [factors_coordinateRestriction_iff, pt_homEquiv_symm, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Corepresented.pointsEquiv H d T y,
      (Corepresented.groupSchemeMap_points d e α y).symm⟩
  · rintro ⟨h, hh⟩
    refine ⟨(Corepresented.pointsEquiv H d T).symm h, ?_⟩
    apply (Corepresented.pointsEquiv F e T).injective
    rw [Corepresented.groupSchemeMap_points, MulEquiv.apply_symm_apply, hh]

/-- Closedness of the actual group-scheme map implies surjectivity of coordinate restriction. -/
theorem coordinateRestriction_surjective
    (hc : IsClosedSubgroup (Corepresented.groupSchemeMap d e α)) :
    Function.Surjective (coordinateRestriction e d α) := by
  let φ : CommRingCat.of B ⟶ CommRingCat.of C :=
    CommRingCat.ofHom (coordinateRestriction e d α).toRingHom
  have hci : IsClosedImmersion (Spec.map φ) := hc
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map φ)).2
  have he : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom = φ := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hh : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom) :=
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of C)).hom).2.comp
      (hs.comp (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv).2)
  rw [he] at hh
  exact hh

/-- Over a field, a finite-type corepresented group and any closed subgroup have one
finite regular subspace whose stabilizer condition detects the actual subgroup range
on every relative scheme. -/
theorem exists_finite_subspace_range_criterion (hR : IsField R) [Algebra.FiniteType R B]
    (hc : IsClosedSubgroup (Corepresented.groupSchemeMap d e α)) :
    letI := hR.toField
    letI := bialgebra e
    letI := bialgebra d
    ∃ V : Submodule R B, Module.Finite R V ∧
      ∀ (T : Over (Spec R)) (x : T ⟶ (Corepresented.groupScheme F e).X),
        x ∈ (SubgroupFunctor.range (Corepresented.groupSchemeMap d e α)).carrier T ↔
          ∀ w : B, w ∈ idealSubspace V (coordinateRestriction e d α).toLinearMap →
            translate
                (e.homEquiv.symm (Corepresented.pointsEquiv F e T x)).hom.toLinearMap w ∈
              tensorSubspace (idealSubspace V (coordinateRestriction e d α).toLinearMap)
                ((algΓ R).obj T).unop := by
  let := hR.toField
  let := bialgebra e
  let := bialgebra d
  let r := coordinateRestrictionBialgHom e d α
  have hsurj : Function.Surjective r := coordinateRestriction_surjective e d α hc
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  obtain ⟨V, hfinite, _, hcrit⟩ := exists_finite_subspace_stabilizer r hsurj
    (Ideal.fg_of_isNoetherianRing _)
  refine ⟨V, hfinite, ?_⟩
  intro T x
  rw [mem_range_iff_coordinate_factors]
  exact (hcrit ((algΓ R).obj T).unop _).symm

end Langlands.GroupScheme.Chevalley
