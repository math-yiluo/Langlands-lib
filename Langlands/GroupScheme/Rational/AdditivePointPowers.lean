import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Mathlib.NumberTheory.LocalField.Basic

/-! # Compact sets containing powers of actual additive points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.VectorGroup

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The actual identity-test point of the vector group with specified field coordinates. -/
def rationalPointOfCoordinates (a : Fin n → R) :
    rationalPoints (groupScheme (CommRingCat.of R) n) :=
  (rationalPointEquiv R (groupScheme (CommRingCat.of R) n).X).symm
    ((spectrumAlgebraPointEquiv R R (MvPolynomial (Fin n) R)).symm
      (AlgPoint.ofAlgHom (MvPolynomial.aeval a)))

@[simp] theorem rationalPointOfCoordinates_left (a : Fin n → R) :
    (rationalPointOfCoordinates R n a).left =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval a).toRingHom) := by
  change ((rationalPointEquiv R (ringTest R (MvPolynomial (Fin n) R))).symm _).left = _
  rw [rationalPointEquiv_symm_left]
  rfl

/-- The global-section coordinates of the point are the prescribed scalar coordinates. -/
theorem coordinates_rationalPointOfCoordinates (a : Fin n → R) :
    (coordinates (CommRingCat.of R) n (Over.mk (𝟙 _))
      (rationalPointOfCoordinates R n a)).toAdd =
        fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv (a i) := by
  funext i
  rw [coordinates_apply, rationalPointOfCoordinates_left]
  change (Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] R).toRingHom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) R))).inv
          (MvPolynomial.X i)) = (Scheme.ΓSpecIso (CommRingCat.of R)).inv (a i)
  have h := congrArg (fun f => f.hom (MvPolynomial.X i))
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom
        (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] R).toRingHom))
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv
      ((MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] R) (MvPolynomial.X i)) =
    (Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] R).toRingHom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) R))).inv
          (MvPolynomial.X i)) at h
  simpa only [MvPolynomial.aeval_X] using h.symm

/-- Raising an actual vector-group point to a natural power multiplies its coordinates. -/
theorem rationalPointOfCoordinates_pow (a : Fin n → R) (k : ℕ) :
    rationalPointOfCoordinates R n a ^ k =
      rationalPointOfCoordinates R n (fun i => k • a i) := by
  apply points_ext
  intro i
  rw [map_pow, toAdd_pow, coordinates_rationalPointOfCoordinates,
    coordinates_rationalPointOfCoordinates]
  change k • (Scheme.ΓSpecIso (CommRingCat.of R)).inv (a i) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv (k • a i)
  exact (map_nsmul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom k (a i)).symm

/-- Scalar coordinates all equal to one give the exact global-section generator. -/
theorem rationalPointOfCoordinates_one :
    rationalPointOfCoordinates R n (fun _ => 1) =
      (coordinates (CommRingCat.of R) n (Over.mk (𝟙 _))).symm
        (Multiplicative.ofAdd (fun _ => 1)) := by
  apply (coordinates (CommRingCat.of R) n (Over.mk (𝟙 _))).injective
  apply Multiplicative.toAdd.injective
  rw [coordinates_rationalPointOfCoordinates, MulEquiv.apply_symm_apply]
  funext i
  exact map_one (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

local instance : IsAffine (groupScheme (CommRingCat.of R) n).X.left := by
  change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) R)))
  infer_instance

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- Scalar coordinates parameterize the actual vector-group points continuously. -/
theorem continuous_rationalPointOfCoordinates :
    let : TopologicalSpace (rationalPoints (groupScheme (CommRingCat.of R) n)) :=
      rationalPointTopology R (groupScheme (CommRingCat.of R) n).X
    Continuous (rationalPointOfCoordinates R n) := by
  let : TopologicalSpace (rationalPoints (groupScheme (CommRingCat.of R) n)) :=
    rationalPointTopology R (groupScheme (CommRingCat.of R) n).X
  exact (rationalPointHomeomorph R (groupScheme (CommRingCat.of R) n).X).symm.continuous.comp
    ((spectrumAlgebraPointHomeomorph R R (MvPolynomial (Fin n) R)).symm.continuous.comp
      (AlgPoint.polynomialPointHomeomorph (R := R) (S := R) (Fin n)).symm.continuous)

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Every actual vector-group point has its nonnegative powers in one compact set. -/
theorem exists_isCompact_powers_rationalPointOfCoordinates (a : Fin n → F) :
    letI : TopologicalSpace (rationalPoints (groupScheme (CommRingCat.of F) n)) :=
      rationalPointTopology F (groupScheme (CommRingCat.of F) n).X
    ∃ C : Set (rationalPoints (groupScheme (CommRingCat.of F) n)),
      IsCompact C ∧ ∀ k : ℕ, rationalPointOfCoordinates F n a ^ k ∈ C := by
  let : TopologicalSpace (rationalPoints (groupScheme (CommRingCat.of F) n)) :=
    rationalPointTopology F (groupScheme (CommRingCat.of F) n).X
  let f : F → rationalPoints (groupScheme (CommRingCat.of F) n) :=
    fun x => rationalPointOfCoordinates F n (fun i => x * a i)
  have hf : Continuous f := (continuous_rationalPointOfCoordinates F n).comp
    (continuous_pi fun i => continuous_id.mul continuous_const)
  refine ⟨f '' {x | ValuativeRel.valuation F x ≤ 1},
    (IsNonarchimedeanLocalField.isCompact_closedBall F 1).image hf, ?_⟩
  intro k
  have hk : ValuativeRel.valuation F (k : F) ≤ 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
        simpa only [Nat.cast_succ] using
          (ValuativeRel.valuation F).map_add_le ih (by simp)
  refine ⟨(k : F), hk, ?_⟩
  simp only [f, rationalPointOfCoordinates_pow, nsmul_eq_mul]

/-- The additive generator with global-section coordinate one has compact powers. -/
theorem exists_isCompact_powers_coordinateOne :
    letI : TopologicalSpace (rationalPoints (groupScheme (CommRingCat.of F) n)) :=
      rationalPointTopology F (groupScheme (CommRingCat.of F) n).X
    ∃ C : Set (rationalPoints (groupScheme (CommRingCat.of F) n)),
      IsCompact C ∧ ∀ k : ℕ,
        ((coordinates (CommRingCat.of F) n (Over.mk (𝟙 _))).symm
          (Multiplicative.ofAdd (fun _ => 1))) ^ k ∈ C := by
  simpa only [rationalPointOfCoordinates_one] using
    exists_isCompact_powers_rationalPointOfCoordinates n F (fun _ => 1)

/-- A vector-group morphism preserves compact containment of powers of the
coordinate-one point, in the actual rational-point topology of the target. -/
theorem exists_isCompact_powers_map_coordinateOne
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    (φ : groupScheme (CommRingCat.of F) n ⟶ G) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∃ C : Set (rationalPoints G), IsCompact C ∧ ∀ k : ℕ,
      (rationalPoints.map φ
        ((coordinates (CommRingCat.of F) n (Over.mk (𝟙 _))).symm
          (Multiplicative.ofAdd (fun _ => 1)))) ^ k ∈ C := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (rationalPoints (groupScheme (CommRingCat.of F) n)) :=
    rationalPointTopology F (groupScheme (CommRingCat.of F) n).X
  obtain ⟨C, hC, hpow⟩ := exists_isCompact_powers_coordinateOne n F
  refine ⟨rationalPoints.map φ '' C,
    hC.image (continuous_rationalPointMap F φ.hom.hom), ?_⟩
  intro k
  exact ⟨_, hpow k, map_pow (rationalPoints.map φ) _ k⟩

end LocalField

end Langlands.GroupScheme.VectorGroup
