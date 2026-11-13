import Langlands.LinearAlgebra.SpecialLinearConjugationScalars

/-! # Normalization of projective special-linear conjugation cocycles -/

noncomputable section

universe u v w

namespace Langlands.LinearAlgebra.SpecialLinearNormalizedCocycle

open Matrix

variable {I : Type u} {R : Type v} [Fintype I] [DecidableEq I] [CommRing R]

/-- The matrix carries the supplied coordinate line into itself. -/
def PreservesCoordinate (p : I) (X : GeneralLinearGroup I R) : Prop :=
  ∀ i, i ≠ p → X i p = 0

/-- Multiplication against a matrix preserving a coordinate line has a single
summand in that column. -/
theorem mul_apply_coordinate (X Y : GeneralLinearGroup I R) (p i : I)
    (hY : PreservesCoordinate p Y) :
    (X * Y) i p = X i p * Y p p := by
  change (∑ j, X i j * Y j p) = _
  exact Finset.sum_eq_single p (by intro j _ hj; simp [hY j hj]) (by simp)

/-- The eigenvalue on a preserved coordinate line is a unit over any commutative ring. -/
theorem isUnit_entry (X : GeneralLinearGroup I R) (p : I)
    (hX : PreservesCoordinate p X) : IsUnit (X p p) := by
  apply IsUnit.of_mul_eq_one_right (X⁻¹ p p)
  rw [← mul_apply_coordinate X⁻¹ X p p hX]
  simp

/-- The unit by which a matrix acts on a preserved coordinate line. -/
def coordinateScalar (X : GeneralLinearGroup I R) (p : I)
    (hX : PreservesCoordinate p X) : Rˣ :=
  (isUnit_entry X p hX).unit

@[simp] theorem coe_coordinateScalar (X : GeneralLinearGroup I R) (p : I)
    (hX : PreservesCoordinate p X) :
    (coordinateScalar X p hX : R) = X p p :=
  (isUnit_entry X p hX).unit_spec

/-- Divide a matrix preserving a coordinate line by its eigenvalue on that line. -/
def normalize (X : GeneralLinearGroup I R) (p : I)
    (hX : PreservesCoordinate p X) : GeneralLinearGroup I R :=
  X * GeneralLinearGroup.scalar I (coordinateScalar X p hX)⁻¹

/-- The normalized matrix fixes the supplied coordinate vector. -/
theorem normalize_column (X : GeneralLinearGroup I R) (p : I)
    (hX : PreservesCoordinate p X) (i : I) :
    normalize X p hX i p = if i = p then 1 else 0 := by
  simp only [normalize, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.mul_diagonal]
  by_cases hi : i = p
  · subst i
    rw [ite_eq_left rfl, ← coe_coordinateScalar X p hX]
    exact Units.mul_inv _
  · rw [ite_eq_right hi, hX i hi, zero_mul]

@[simp] theorem normalize_entry (X : GeneralLinearGroup I R) (p : I)
    (hX : PreservesCoordinate p X) : normalize X p hX p p = 1 := by
  simp [normalize_column]

theorem normalize_preservesCoordinate (X : GeneralLinearGroup I R) (p : I)
    (hX : PreservesCoordinate p X) : PreservesCoordinate p (normalize X p hX) := by
  intro i hi
  simp [normalize_column, hi]

/-- Scalar normalization does not change conjugation on invertible matrices. -/
theorem normalize_conjugate (X : GeneralLinearGroup I R) (p : I)
    (hX : PreservesCoordinate p X) (g : GeneralLinearGroup I R) :
    normalize X p hX * g * (normalize X p hX)⁻¹ = X * g * X⁻¹ := by
  let s := GeneralLinearGroup.scalar I (coordinateScalar X p hX)⁻¹
  have hs : s * g = g * s := by
    have hcenter : s ∈ Subgroup.center _ := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    exact (Subgroup.mem_center_iff.mp hcenter g).symm
  change (X * s) * _ * (X * s)⁻¹ = _
  calc
    (X * s) * g * (X * s)⁻¹ = X * (s * g) * s⁻¹ * X⁻¹ := by group
    _ = X * g * X⁻¹ := by rw [hs]; group

/-- Coordinate-line preservation survives any change of coefficients. -/
theorem preservesCoordinate_map {S : Type*} [CommRing S] (f : R →+* S)
    (X : GeneralLinearGroup I R) (p : I) (hX : PreservesCoordinate p X) :
    PreservesCoordinate p (GeneralLinearGroup.map f X) := by
  intro i hi
  change f (X i p) = 0
  simp [hX i hi]

/-- A coefficient map preserves the normalized diagonal entry. -/
theorem map_normalize_entry {S : Type*} [CommRing S] (f : R →+* S)
    (X : GeneralLinearGroup I R) (p : I) (hX : PreservesCoordinate p X) :
    GeneralLinearGroup.map f (normalize X p hX) p p = 1 := by
  change f (normalize X p hX p p) = 1
  simp

/-- Scalar normalization keeps the same conjugation after any coefficient map. -/
theorem map_normalize_conjugate {S : Type*} [CommRing S] (f : R →+* S)
    (X : GeneralLinearGroup I R) (p : I) (hX : PreservesCoordinate p X)
    (g : GeneralLinearGroup I S) :
    GeneralLinearGroup.map f (normalize X p hX) * g *
        (GeneralLinearGroup.map f (normalize X p hX))⁻¹ =
      GeneralLinearGroup.map f X * g * (GeneralLinearGroup.map f X)⁻¹ := by
  let s := GeneralLinearGroup.scalar I
    (Units.map f.toMonoidHom (coordinateScalar X p hX)⁻¹)
  have heq : GeneralLinearGroup.map f (normalize X p hX) =
      GeneralLinearGroup.map f X * s := by
    simp [normalize, s, GeneralLinearGroup.map_scalar]
  have hs : s * g = g * s := by
    have hcenter : s ∈ Subgroup.center _ := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    exact (Subgroup.mem_center_iff.mp hcenter g).symm
  rw [heq]
  calc
    (GeneralLinearGroup.map f X * s) * g *
        (GeneralLinearGroup.map f X * s)⁻¹ =
      GeneralLinearGroup.map f X * (s * g) * s⁻¹ *
        (GeneralLinearGroup.map f X)⁻¹ := by group
    _ = _ := by rw [hs]; group

variable {H : Type w} [Group H]

/-- A projective matrix cocycle preserving a coordinate line becomes an honest
cocycle after division by its eigenvalue on that line. -/
theorem normalize_cocycle (α : H →* (R ≃+* R))
    (x : H → GeneralLinearGroup I R) (p : I)
    (hx : ∀ σ, PreservesCoordinate p (x σ))
    (hproj : ∀ σ τ (g : SpecialLinearGroup I R),
      x (σ * τ) * SpecialLinearGroup.toGL g * (x (σ * τ))⁻¹ =
        (x σ * GeneralLinearGroup.map (α σ).toRingHom (x τ)) *
          SpecialLinearGroup.toGL g *
          (x σ * GeneralLinearGroup.map (α σ).toRingHom (x τ))⁻¹) :
    ∀ σ τ, normalize (x (σ * τ)) p (hx (σ * τ)) =
      normalize (x σ) p (hx σ) *
        GeneralLinearGroup.map (α σ).toRingHom (normalize (x τ) p (hx τ)) := by
  intro σ τ
  apply SpecialLinearConjugation.eq_of_conjugation_eq_of_entry_eq_one _ _ p
  · exact normalize_entry _ _ _
  · rw [mul_apply_coordinate _ _ p p
      (preservesCoordinate_map _ _ p (normalize_preservesCoordinate _ _ _))]
    simp
  · intro g
    rw [normalize_conjugate]
    calc
      x (σ * τ) * SpecialLinearGroup.toGL g * (x (σ * τ))⁻¹ =
          (x σ * GeneralLinearGroup.map (α σ).toRingHom (x τ)) *
            SpecialLinearGroup.toGL g *
            (x σ * GeneralLinearGroup.map (α σ).toRingHom (x τ))⁻¹ := hproj σ τ g
      _ = x σ * (GeneralLinearGroup.map (α σ).toRingHom (x τ) *
          SpecialLinearGroup.toGL g *
          (GeneralLinearGroup.map (α σ).toRingHom (x τ))⁻¹) * (x σ)⁻¹ := by group
      _ = x σ * (GeneralLinearGroup.map (α σ).toRingHom
          (normalize (x τ) p (hx τ)) * SpecialLinearGroup.toGL g *
          (GeneralLinearGroup.map (α σ).toRingHom
            (normalize (x τ) p (hx τ)))⁻¹) * (x σ)⁻¹ := by
        rw [map_normalize_conjugate]
      _ = (normalize (x σ) p (hx σ) *
          GeneralLinearGroup.map (α σ).toRingHom (normalize (x τ) p (hx τ))) *
          SpecialLinearGroup.toGL g *
          (normalize (x σ) p (hx σ) *
            GeneralLinearGroup.map (α σ).toRingHom (normalize (x τ) p (hx τ)))⁻¹ := by
        rw [← normalize_conjugate (x σ) p (hx σ)]
        group


end Langlands.LinearAlgebra.SpecialLinearNormalizedCocycle
