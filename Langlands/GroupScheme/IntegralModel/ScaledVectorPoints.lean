import Langlands.GroupScheme.IntegralModel.ScaledVector

/-! # Exact integral-point coordinates of scaled vector models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace VectorGroup

variable {R A : CommRingCat.{u}} {n : ℕ}

/-- Scaling a section scales its coefficient-ring coordinates. -/
theorem sectionCoordinates_scalar (c : R) (x : rationalPoints (groupScheme R n))
    (j : Fin n) :
    (sectionCoordinates R n (x ≫ (scalar c).hom.hom)).toAdd j =
      c * (sectionCoordinates R n x).toAdd j := by
  rw [sectionCoordinates_apply, coordinates_scalar, map_mul]
  have hc : (Scheme.ΓSpecIso R).hom.hom
      (scalarMap (Over.mk (𝟙 (Spec R))) c) = c := by
    change ((Scheme.ΓSpecIso R).inv ≫ (𝟙 (Spec R) : Spec R ⟶ Spec R).appTop ≫
      (Scheme.ΓSpecIso R).hom) c = c
    simp
  rw [hc]
  rfl

/-- Changing a section's base changes each coordinate by the given ring map. -/
theorem sectionCoordinates_baseChange (ρ : R ⟶ A)
    (x : rationalPoints (groupScheme R n)) (j : Fin n) :
    (sectionCoordinates A n
      (baseChangeSectionHom (Spec.map ρ) (groupScheme R n) x ≫
        (baseChangeIso ρ).hom.hom.hom)).toAdd j =
      ρ.hom ((sectionCoordinates R n x).toAdd j) := by
  rw [sectionCoordinates_apply, coordinates_baseChangeIso_hom]
  have hb : baseChangePointsEquiv (Spec.map ρ) (groupScheme R n) (Over.mk (𝟙 _))
      (baseChangeSectionHom (Spec.map ρ) (groupScheme R n) x) =
      (Over.homMk (Spec.map ρ) (by simp) :
        (Over.map (Spec.map ρ)).obj (Over.mk (𝟙 _)) ⟶ Over.mk (𝟙 _)) ≫ x := by
    apply Over.OverMorphism.ext
    simp only [baseChangePointsEquiv_left, Over.comp_left, Over.homMk_left]
    exact baseChangeSectionHom_fst (Spec.map ρ) (groupScheme R n) x
  change (Scheme.ΓSpecIso A).hom.hom
      ((coordinates R n ((Over.map (Spec.map ρ)).obj (Over.mk (𝟙 _)))
        (baseChangePointsEquiv (Spec.map ρ) (groupScheme R n) (Over.mk (𝟙 _))
          (baseChangeSectionHom (Spec.map ρ) (groupScheme R n) x))).toAdd j) = _
  rw [hb, coordinates_comp]
  change ((Spec.map ρ).appTop ≫ (Scheme.ΓSpecIso A).hom) _ =
    ρ.hom ((Scheme.ΓSpecIso R).hom.hom _)
  rw [Scheme.ΓSpecIso_naturality]
  rfl

end VectorGroup
namespace IntegralModel

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (n : ℕ)

/-- The principal vector lattice consists of the vectors with coordinates
`t * a_j` for integral coefficients `a_j`. The scalar may be zero. -/
def principalVectorLattice (t : K) : Submodule R (Fin n → K) where
  carrier := {w | ∃ v : Fin n → R, ∀ j, w j = t * algebraMap R K (v j)}
  zero_mem' := ⟨0, by intro j; simp⟩
  add_mem' := by
    rintro w z ⟨v, hv⟩ ⟨v', hv'⟩
    refine ⟨v + v', ?_⟩
    intro j
    simp only [Pi.add_apply, map_add, mul_add, hv j, hv' j]
  smul_mem' := by
    rintro c w ⟨v, hv⟩
    refine ⟨c • v, ?_⟩
    intro j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hv j, Algebra.smul_def]
    ring

/-- The actual generic point of an integral section has the scaled coordinates. -/
theorem scaledVector_integralPointMap (t : Kˣ)
    (x : (scaledVector R K n t).integralSections) (j : Fin n) :
    (VectorGroup.sectionCoordinates (CommRingCat.of K) n
      ((scaledVector R K n t).integralPointMap x)).toAdd j =
      (t : K) * algebraMap R K
        ((VectorGroup.sectionCoordinates (CommRingCat.of R) n x).toAdd j) := by
  change (VectorGroup.sectionCoordinates (CommRingCat.of K) n
    ((baseChangeSectionHom (Spec.algebraMap R K)
        (VectorGroup.groupScheme (CommRingCat.of R) n) x ≫
          (VectorGroup.baseChangeIso (CommRingCat.ofHom (algebraMap R K))).hom.hom.hom) ≫
            (VectorGroup.scalar (t : K)).hom.hom)).toAdd j = _
  rw [VectorGroup.sectionCoordinates_scalar, VectorGroup.sectionCoordinates_baseChange]
  rfl

/-- The exact image is the principal lattice `t · Rⁿ` in the supplied coordinates. -/
theorem scaledVector_mem_integralPoints (t : Kˣ)
    (g : rationalPoints (VectorGroup.groupScheme (CommRingCat.of K) n)) :
    g ∈ (scaledVector R K n t).integralPoints ↔
      ∃ v : Fin n → R, ∀ j,
        (VectorGroup.sectionCoordinates (CommRingCat.of K) n g).toAdd j =
          (t : K) * algebraMap R K (v j) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(VectorGroup.sectionCoordinates (CommRingCat.of R) n x).toAdd,
      scaledVector_integralPointMap R K n t x⟩
  · rintro ⟨v, hv⟩
    refine ⟨(VectorGroup.sectionCoordinates (CommRingCat.of R) n).symm
      (Multiplicative.ofAdd v), ?_⟩
    apply (VectorGroup.sectionCoordinates (CommRingCat.of K) n).injective
    apply Multiplicative.toAdd.injective
    funext j
    rw [scaledVector_integralPointMap, MulEquiv.apply_symm_apply]
    exact (hv j).symm

/-- The actual integral-point image agrees with the explicitly defined
principal vector lattice under the canonical section coordinates. -/
theorem scaledVector_mem_integralPoints_iff_mem_principalVectorLattice (t : Kˣ)
    (g : rationalPoints (VectorGroup.groupScheme (CommRingCat.of K) n)) :
    g ∈ (scaledVector R K n t).integralPoints ↔
      (VectorGroup.sectionCoordinates (CommRingCat.of K) n g).toAdd ∈
        principalVectorLattice R K n (t : K) :=
  scaledVector_mem_integralPoints R K n t g

end IntegralModel
end Langlands.GroupScheme
