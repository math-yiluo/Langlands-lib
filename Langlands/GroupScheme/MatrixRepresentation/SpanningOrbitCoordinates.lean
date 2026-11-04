import Langlands.GroupScheme.MatrixRepresentation.OrbitCoordinates
import Langlands.GroupScheme.MatrixRepresentation.NormalKernelTensor
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # A spanning representation with the same coordinate-line stabilizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

/-- A matrix applied to a standard basis vector is the corresponding column. -/
theorem mulVec_single_one_eq_column {α : Type*} [NonAssocSemiring α] {n m : Type}
    [Fintype m] [DecidableEq m] (B : Matrix n m α) (s : m) :
    B *ᵥ Pi.single s 1 = fun r => B r s := by
  rw [Matrix.mulVec_single_one]
  rfl

section General

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Two representations with distinguished coordinates have the same unit-scalar stabilizer of
their coordinate lines on every relative scheme test, with units of the actual global-section
ring of the test. -/
def SameCoordinateLineStabilizer (ρ : MatrixRepresentation G n) (j : n)
    (σ : MatrixRepresentation G m) (s : m) : Prop :=
  ∀ (Z : Over (Spec R)) (x : Z ⟶ G.X),
    (∃ c : Γ(Z.left, ⊤)ˣ,
      (σ.pointMatrix Z x : Matrix m m Γ(Z.left, ⊤)) *ᵥ Pi.single s 1 =
        (c : Γ(Z.left, ⊤)) • (Pi.single s 1 : m → Γ(Z.left, ⊤))) ↔
    (∃ c : Γ(Z.left, ⊤)ˣ,
      (ρ.pointMatrix Z x : Matrix n n Γ(Z.left, ⊤)) *ᵥ Pi.single j 1 =
        (c : Γ(Z.left, ⊤)) • (Pi.single j 1 : n → Γ(Z.left, ⊤)))

variable (ρ : MatrixRepresentation G n) (B : Matrix n m R) (C : Matrix m n R)
  (hCB : C * B = 1) (hstable : ρ.IsStableCoordinates B C)

/-- On every test, the restricted matrix is the projected ambient matrix. -/
theorem restrictCoordinates_pointMatrix_coe (T : Over (Spec R)) (x : T ⟶ G.X) :
    ((restrictCoordinates ρ B C hCB hstable).pointMatrix T x : Matrix m m Γ(T.left, ⊤)) =
      C.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
        B.map (scalarMap T) := by
  rw [restrictCoordinates_pointMatrix]
  rfl

/-- The rational matrices of the restriction are the projected ambient rational matrices. -/
theorem rationalMatrix_restrictCoordinates (g : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    ((restrictCoordinates ρ B C hCB hstable).rationalMatrix g : Matrix m m R) =
      C * (ρ.rationalMatrix g : Matrix n n R) * B := by
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  have hB : (B.map (scalarMap (Over.mk (𝟙 (Spec R))))).map e.toRingHom = B := by
    ext r s
    exact e.apply_symm_apply _
  have hC : (C.map (scalarMap (Over.mk (𝟙 (Spec R))))).map e.toRingHom = C := by
    ext r s
    exact e.apply_symm_apply _
  have hM : ((ρ.pointMatrix (Over.mk (𝟙 (Spec R)))) g).val.map e.toRingHom =
      (ρ.rationalMatrix g : Matrix n n R) := rfl
  change (((restrictCoordinates ρ B C hCB hstable).pointMatrix (Over.mk (𝟙 (Spec R))) g :
      Matrix m m Γ((Over.mk (𝟙 (Spec R))).left, ⊤))).map e.toRingHom = _
  rw [restrictCoordinates_pointMatrix_coe, Matrix.map_mul, Matrix.map_mul, hB, hC, hM]

/-- If the inclusion sends the distinguished coordinate vector to the ambient distinguished
coordinate vector, the restriction has the same coordinate-line stabilizer on all tests. -/
theorem sameCoordinateLineStabilizer_restrictCoordinates (j : n) (s : m)
    (hs : (fun r => B r s) = Pi.single j 1) :
    SameCoordinateLineStabilizer ρ j (restrictCoordinates ρ B C hCB hstable) s := by
  intro Z x
  have hBs : B.map (scalarMap Z) *ᵥ Pi.single s 1 = Pi.single j 1 := by
    rw [mulVec_single_one_eq_column]
    change (fun r => scalarMap Z ((fun r => B r s) r)) = _
    rw [hs]
    exact scalarMap_single Z j
  have hCB' : C.map (scalarMap Z) * B.map (scalarMap Z) = 1 := by
    rw [← Matrix.map_mul, hCB, Matrix.map_one _ (map_zero _) (map_one _)]
  have hCj : C.map (scalarMap Z) *ᵥ Pi.single j 1 = Pi.single s 1 := by
    rw [← hBs, Matrix.mulVec_mulVec, hCB', Matrix.one_mulVec]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hBs, Matrix.mulVec_mulVec, restrictCoordinates_intertwines ρ B C hCB hstable Z x,
      ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [restrictCoordinates_pointMatrix_coe, ← Matrix.mulVec_mulVec, hBs,
      ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hCj]

end General

section Field

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- If every column of the inclusion lies in the rational orbit of the ambient distinguished
vector and the distinguished column is that vector, then the rational orbit of the restricted
distinguished vector spans the whole restricted coordinate space. -/
theorem span_restrictCoordinates_orbit_eq_top (ρ : MatrixRepresentation G n)
    (B : Matrix n m k) (C : Matrix m n k) (hCB : C * B = 1)
    (hstable : ρ.IsStableCoordinates B C) (j : n) (s : m)
    (hs : (fun r => B r s) = Pi.single j 1)
    (hcols : ∀ t, ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (fun r => B r t) = (ρ.rationalMatrix g : Matrix n n k) *ᵥ Pi.single j 1) :
    Submodule.span k (Set.range fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
      ((restrictCoordinates ρ B C hCB hstable).rationalMatrix g : Matrix m m k) *ᵥ
        (Pi.single s 1 : m → k)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun k m).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  obtain ⟨g, hg⟩ := hcols t
  apply Submodule.subset_span
  refine ⟨g, ?_⟩
  simp only [Pi.basisFun_apply]
  rw [rationalMatrix_restrictCoordinates, ← Matrix.mulVec_mulVec,
    mulVec_single_one_eq_column B s, hs, ← Matrix.mulVec_mulVec, ← hg,
    ← mulVec_single_one_eq_column B t, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec]

/-- Over an algebraically closed field, a coordinate line of a finite representation of a smooth
group has the same all-test unit-scalar stabilizer as a coordinate line of a finite
representation in which the rational orbit of the distinguished vector spans. -/
theorem exists_spanning_sameCoordinateLineStabilizer [IsAlgClosed k] [Smooth G.X.hom]
    (ρ : MatrixRepresentation G n) (j : n) :
    ∃ (d : ℕ) (s : Fin (d + 1)) (σ : MatrixRepresentation G (Fin (d + 1))),
      SameCoordinateLineStabilizer ρ j σ s ∧
      Submodule.span k (Set.range fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
        (σ.rationalMatrix g : Matrix (Fin (d + 1)) (Fin (d + 1)) k) *ᵥ
          (Pi.single s 1 : Fin (d + 1) → k)) = ⊤ := by
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ G.X.hom
  obtain ⟨d, B, C, hCB, hcols, hstable, s, hs⟩ := ρ.exists_rationalOrbit_coordinates j
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by have := s.pos; omega⟩
  exact ⟨d', s, restrictCoordinates ρ B C hCB hstable,
    sameCoordinateLineStabilizer_restrictCoordinates ρ B C hCB hstable j s hs,
    span_restrictCoordinates_orbit_eq_top ρ B C hCB hstable j s hs hcols⟩

end Field

end Langlands.GroupScheme.MatrixRepresentation
