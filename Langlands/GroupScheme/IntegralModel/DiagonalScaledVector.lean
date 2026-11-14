import Langlands.GroupScheme.VectorDiagonalKernel
import Langlands.GroupScheme.IntegralModel.ScaledVectorPoints

/-! # Integral vector models with independent coordinate scales -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace VectorGroup

variable {R : CommRingCat.{u}} {n : ℕ}

/-- The diagonal map multiplies each coefficient-ring section coordinate by its
corresponding coefficient. -/
theorem sectionCoordinates_diagonal (c : Fin n → R)
    (x : rationalPoints (groupScheme R n)) (j : Fin n) :
    (sectionCoordinates R n (x ≫ (diagonal c).hom.hom)).toAdd j =
      c j * (sectionCoordinates R n x).toAdd j := by
  rw [sectionCoordinates_apply, coordinates_diagonal, map_mul]
  have hc : (Scheme.ΓSpecIso R).hom.hom
      (scalarMap (Over.mk (𝟙 (Spec R))) (c j)) = c j := by
    change ((Scheme.ΓSpecIso R).inv ≫ (𝟙 (Spec R) : Spec R ⟶ Spec R).appTop ≫
      (Scheme.ΓSpecIso R).hom) (c j) = c j
    simp
  rw [hc]
  rfl

end VectorGroup

namespace IntegralModel

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (n : ℕ)

/-- The standard polynomial integral model with independently scaled generic
coordinates. -/
def diagonalScaledVector (t : Fin n → Kˣ) :
    IntegralModel R K (VectorGroup.groupScheme (CommRingCat.of K) n) where
  group := VectorGroup.groupScheme (CommRingCat.of R) n
  affine := by
    change IsAffineHom
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))))
    infer_instance
  flat := by
    have := VectorGroup.smooth (CommRingCat.of R) n
    infer_instance
  finiteType := by
    have := VectorGroup.smooth (CommRingCat.of R) n
    infer_instance
  genericIso := VectorGroup.baseChangeIso
    (CommRingCat.ofHom (algebraMap R K)) ≪≫ VectorGroup.diagonalIso t

theorem diagonalScaledVector_isSmooth (t : Fin n → Kˣ) :
    (diagonalScaledVector R K n t).IsSmooth :=
  VectorGroup.smooth (CommRingCat.of R) n

theorem diagonalScaledVector_hasGeometricallyConnectedFibres (t : Fin n → Kˣ) :
    (diagonalScaledVector R K n t).HasGeometricallyConnectedFibres :=
  VectorGroup.geometricallyConnected (CommRingCat.of R) n

/-- The lattice with one principal fractional ideal in each coordinate. -/
def diagonalVectorLattice (t : Fin n → K) : Submodule R (Fin n → K) where
  carrier := {w | ∃ v : Fin n → R, ∀ j, w j = t j * algebraMap R K (v j)}
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

/-- The integral-section map has exactly the prescribed coordinate scales. -/
theorem diagonalScaledVector_integralPointMap (t : Fin n → Kˣ)
    (x : (diagonalScaledVector R K n t).integralSections) (j : Fin n) :
    (VectorGroup.sectionCoordinates (CommRingCat.of K) n
      ((diagonalScaledVector R K n t).integralPointMap x)).toAdd j =
      (t j : K) * algebraMap R K
        ((VectorGroup.sectionCoordinates (CommRingCat.of R) n x).toAdd j) := by
  change (VectorGroup.sectionCoordinates (CommRingCat.of K) n
    ((baseChangeSectionHom (Spec.algebraMap R K)
        (VectorGroup.groupScheme (CommRingCat.of R) n) x ≫
          (VectorGroup.baseChangeIso (CommRingCat.ofHom (algebraMap R K))).hom.hom.hom) ≫
            (VectorGroup.diagonal (fun j => (t j : K))).hom.hom)).toAdd j = _
  rw [VectorGroup.sectionCoordinates_diagonal, VectorGroup.sectionCoordinates_baseChange]
  rfl

/-- The exact generic-point image is the diagonal lattice in the canonical
section coordinates. -/
theorem diagonalScaledVector_mem_integralPoints (t : Fin n → Kˣ)
    (g : rationalPoints (VectorGroup.groupScheme (CommRingCat.of K) n)) :
    g ∈ (diagonalScaledVector R K n t).integralPoints ↔
      (VectorGroup.sectionCoordinates (CommRingCat.of K) n g).toAdd ∈
        diagonalVectorLattice R K n (fun j => (t j : K)) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(VectorGroup.sectionCoordinates (CommRingCat.of R) n x).toAdd,
      diagonalScaledVector_integralPointMap R K n t x⟩
  · rintro ⟨v, hv⟩
    refine ⟨(VectorGroup.sectionCoordinates (CommRingCat.of R) n).symm
      (Multiplicative.ofAdd v), ?_⟩
    apply (VectorGroup.sectionCoordinates (CommRingCat.of K) n).injective
    apply Multiplicative.toAdd.injective
    funext j
    rw [diagonalScaledVector_integralPointMap, MulEquiv.apply_symm_apply]
    exact (hv j).symm

variable {R K n}

/-- The coefficient equations make the integral diagonal map extend the
identity on the actual generic vector group. -/
def diagonalScaledVectorTransition (s t : Fin n → Kˣ) (c : Fin n → R)
    (h : ∀ j, algebraMap R K (c j) * (t j : K) = s j) :
    (diagonalScaledVector R K n s).Hom (diagonalScaledVector R K n t) (𝟙 _) where
  hom := VectorGroup.diagonal c
  generic_comm := by
    change (GroupScheme.baseChange (Spec.algebraMap R K)).map (VectorGroup.diagonal c) ≫
        ((VectorGroup.baseChangeIso _).hom ≫ VectorGroup.diagonal (fun j => (t j : K))) =
      ((VectorGroup.baseChangeIso _).hom ≫ VectorGroup.diagonal (fun j => (s j : K))) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, ← VectorGroup.diagonal_baseChange,
      Category.assoc, VectorGroup.diagonal_comp]
    have hc : (fun j => (CommRingCat.ofHom (algebraMap R K)).hom (c j)) *
        (fun j => (t j : K)) = (fun j => (s j : K)) := funext h
    rw [hc]

variable [IsLocalRing R]

/-- Every compatible extension has the explicit diagonal map's actual
special-fibre kernel geometry. The residue coefficients can vanish independently. -/
theorem diagonalScaledVector_kernel_properties
    (s t : Fin n → Kˣ) (c : Fin n → R)
    (h : ∀ j, algebraMap R K (c j) * (t j : K) = s j)
    (φ : (diagonalScaledVector R K n s).Hom (diagonalScaledVector R K n t) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  have hφ := φ.hom_eq (diagonalScaledVectorTransition s t c h)
  change Smooth (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom)).X.hom ∧
    ConnectedSpace (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom)).X.left ∧
      IsUnipotent (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom))
  rw [hφ]
  exact VectorGroup.diagonal_baseChange_kernel_properties
    (CommRingCat.ofHom (IsLocalRing.residue R)) c

end IntegralModel
end Langlands.GroupScheme
