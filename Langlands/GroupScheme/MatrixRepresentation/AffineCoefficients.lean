import Langlands.LinearAlgebra.AdicCoefficientSeparation
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces
import Langlands.GroupScheme.MatrixRepresentation.RationalIrreducibility
import Langlands.GroupScheme.Rational.SubquotientSpectralIntegrality
import Langlands.LinearAlgebra.IrreducibleRepresentationSpan

/-! # Linear coefficients of the universal affine representation matrix -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation.AffineCoefficients

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n)

/-- Applying a linear functional to the universal matrix. -/
def coefficientMap :
    (CharacterUnits.Coord G →ₗ[k] k) →ₗ[k] Matrix n n k where
  toFun ℓ := ρ.universalCharacterMatrix.map ℓ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual matrix at any affine test is an evaluation of the universal matrix. -/
theorem universalCharacterMatrix_map
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) :
    ρ.universalCharacterMatrix.map (Lie.pointCoordinates G x) =
      (ρ.affineMatrix A x : Matrix n n A) := by
  have h := ρ.affineMatrix_naturality
    (CommAlgCat.ofHom (Lie.pointCoordinates G x)) (CharacterUnits.universalPoint G)
  rw [← GroupScheme.affinePointMap_apply,
    CharacterUnits.affinePointMap_universalPoint] at h
  exact (congrArg (fun M => M.val) h).symm

/-- The augmentation evaluates the universal representation matrix to identity. -/
theorem universalCharacterMatrix_origin :
    ρ.universalCharacterMatrix.map (Lie.coordinateOrigin G) = 1 := by
  calc
    ρ.universalCharacterMatrix.map (Lie.coordinateOrigin G) =
        (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) k) 1 : Matrix n n k) :=
      universalCharacterMatrix_map ρ (CommAlgCat.of (CommRingCat.of k) k) 1
    _ = 1 := congrArg Units.val
      (map_one (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) k)))

/-- Coefficient extraction commutes with applying a constant vector. -/
theorem coefficientMap_mulVec (ℓ : CharacterUnits.Coord G →ₗ[k] k) (v : n → k) :
    coefficientMap ρ ℓ *ᵥ v =
      fun i => ℓ ((ρ.universalCharacterMatrix *ᵥ
        (fun j => algebraMap k (CharacterUnits.Coord G) (v j))) i) := by
  funext i
  have hs (a : CharacterUnits.Coord G) (c : k) :
      ℓ (a * algebraMap k (CharacterUnits.Coord G) c) = ℓ a * c := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  change (∑ j, ℓ (ρ.universalCharacterMatrix i j) * v j) =
    ℓ (∑ j, ρ.universalCharacterMatrix i j *
      algebraMap k (CharacterUnits.Coord G) (v j))
  simp only [map_sum, hs]

/-- All-affine-test stability is stability under every universal coefficient matrix. -/
theorem isStableSubspace_iff (W : Submodule k (n → k)) :
    ρ.IsStableSubspace W ↔
      ∀ ℓ : CharacterUnits.Coord G →ₗ[k] k, ∀ v ∈ W, coefficientMap ρ ℓ *ᵥ v ∈ W := by
  constructor
  · intro h ℓ v hv
    rw [coefficientMap_mulVec]
    exact h _ (CharacterUnits.universalPoint G) v hv ℓ
  · intro h A x v hv ℓ
    let φ := Lie.pointCoordinates G x
    have hc := h (ℓ.comp φ.toLinearMap) v hv
    rw [coefficientMap_mulVec] at hc
    convert hc using 1
    funext i
    have hm := congrArg (fun M => (M *ᵥ (fun j => algebraMap k A (v j))) i)
      (universalCharacterMatrix_map ρ A x)
    dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [← hm]
    have hv' : φ.toRingHom ∘ (fun j => algebraMap k (CharacterUnits.Coord G) (v j)) =
        (fun j => algebraMap k A (v j)) := by
      funext j
      exact φ.commutes _
    exact congrArg ℓ (by
      have hmap := φ.toRingHom.map_mulVec ρ.universalCharacterMatrix
        (fun j => algebraMap k (CharacterUnits.Coord G) (v j)) i
      rw [hv'] at hmap
      exact hmap.symm)

/-- Every rational-point matrix belongs to the range of universal coefficient extraction. -/
theorem rationalMatrix_mem_range (g : rationalPoints G) :
    (ρ.rationalMatrix g : Matrix n n k) ∈ LinearMap.range (coefficientMap ρ) := by
  refine ⟨(Lie.pointCoordinates G (rationalAffinePoint g)).toLinearMap, ?_⟩
  change ρ.universalCharacterMatrix.map (Lie.pointCoordinates G (rationalAffinePoint g)) = _
  exact (universalCharacterMatrix_map ρ (CommAlgCat.of (CommRingCat.of k) k)
    (rationalAffinePoint g)).trans
      (congrArg Units.val (rationalMatrix_eq_affineMatrix ρ g).symm)

/-- For an irreducible actual representation, its universal coefficient map is onto. -/
theorem coefficientMap_surjective [IsAlgClosed k] [IsReduced G.X.left]
    [LocallyOfFiniteType G.X.hom] (hρ : ρ.IsIrreducible) :
    Function.Surjective (coefficientMap ρ) := by
  have hrep : ρ.rationalRepresentation =
      Langlands.LinearAlgebra.matrixAction ρ.rationalMatrix := by
    ext g v i
    rfl
  let : Representation.IsIrreducible
      (Langlands.LinearAlgebra.matrixAction ρ.rationalMatrix) := hrep ▸ hρ.rationalRepresentation
  have hfull := Langlands.LinearAlgebra.matrix_span_eq_top_of_irreducible ρ.rationalMatrix
  have hle : Submodule.span k (Set.range fun g => (ρ.rationalMatrix g : Matrix n n k)) ≤
      LinearMap.range (coefficientMap ρ) :=
    Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact rationalMatrix_mem_range ρ g)
  rw [hfull] at hle
  exact LinearMap.range_eq_top.mp (top_unique hle)

/-- The finite-dimensional subspace spanned by all universal matrix entries. -/
def coefficientSpace : Submodule k (CharacterUnits.Coord G) :=
  Submodule.span k (Set.range fun ij : n × n => ρ.universalCharacterMatrix ij.1 ij.2)

instance : FiniteDimensional k (coefficientSpace ρ) :=
  FiniteDimensional.span_of_finite k (Set.finite_range _)

theorem universalCharacterMatrix_mem (i j : n) :
    ρ.universalCharacterMatrix i j ∈ coefficientSpace ρ :=
  Submodule.subset_span ⟨(i, j), rfl⟩

/-- One ideal-power quotient reproduces every universal coefficient matrix. -/
theorem exists_quotient_coefficients
    [IsNoetherianRing (CharacterUnits.Coord G)] [IsDomain (CharacterUnits.Coord G)]
    (I : Ideal (CharacterUnits.Coord G)) (hI : I ≠ ⊤) :
    ∃ N, ∀ ℓ : CharacterUnits.Coord G →ₗ[k] k,
      ∃ q : ((CharacterUnits.Coord G) ⧸ I ^ N) →ₗ[k] k,
        (ρ.universalCharacterMatrix.map (Ideal.Quotient.mk (I ^ N))).map q =
          coefficientMap ρ ℓ := by
  obtain ⟨N, hN⟩ := Langlands.LinearAlgebra.AdicCoefficientSeparation.exists_quotient_functionals
    I hI (coefficientSpace ρ)
  refine ⟨N, fun ℓ => ?_⟩
  obtain ⟨q, hq⟩ := hN ℓ
  refine ⟨q, ?_⟩
  ext i j
  exact hq _ (universalCharacterMatrix_mem ρ i j)

/-- At one ideal-power quotient, linear coefficients already give every matrix
of an actual irreducible representation on its full original coordinate space. -/
theorem exists_quotient_surjective [IsAlgClosed k] [IsReduced G.X.left]
    [LocallyOfFiniteType G.X.hom]
    [IsNoetherianRing (CharacterUnits.Coord G)] [IsDomain (CharacterUnits.Coord G)]
    (hρ : ρ.IsIrreducible) (I : Ideal (CharacterUnits.Coord G)) (hI : I ≠ ⊤) :
    ∃ N, ∀ M : Matrix n n k,
      ∃ q : ((CharacterUnits.Coord G) ⧸ I ^ N) →ₗ[k] k,
        (ρ.universalCharacterMatrix.map (Ideal.Quotient.mk (I ^ N))).map q = M := by
  obtain ⟨N, hN⟩ := exists_quotient_coefficients ρ I hI
  refine ⟨N, fun M => ?_⟩
  obtain ⟨ℓ, rfl⟩ := coefficientMap_surjective ρ hρ M
  exact hN ℓ

end Langlands.GroupScheme.MatrixRepresentation.AffineCoefficients
