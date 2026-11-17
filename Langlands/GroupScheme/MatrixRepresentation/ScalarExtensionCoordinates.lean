import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.Torus.CocharacterSplitting

/-! # Scalar-extension coordinates and descent of actual intertwiners -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

section Tests

variable (S : Type u) [CommRing S] [Algebra K S] [Algebra k S] [IsScalarTower k K S]

/-- Lift a point over a compatible extension-field algebra to the base-changed group. -/
def scalarExtensionPoint
    (x : G.affinePoints (CommAlgCat.of (CommRingCat.of k) S)) :
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).affinePoints
      (CommAlgCat.of (CommRingCat.of K) S) :=
  (baseChangePointsEquiv (algebraBaseMap k K) G _).symm
    ((CocharacterSplitting.testIso K S).hom ≫ x)

/-- On a common test ring, a base-changed representation has the original affine matrix. -/
theorem affineMatrix_scalarExtensionPoint (ρ : MatrixRepresentation G n)
    (x : G.affinePoints (CommAlgCat.of (CommRingCat.of k) S)) :
    (ρ.baseChange (algebraBaseMap k K)).affineMatrix
      (CommAlgCat.of (CommRingCat.of K) S) (scalarExtensionPoint S x) =
        ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) S) x := by
  let A := CommAlgCat.of (CommRingCat.of K) S
  let A₀ := CommAlgCat.of (CommRingCat.of k) S
  have hq : Function.Injective (Corepresented.affineSectionsIso A).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
  have h := (ρ.baseChange (algebraBaseMap k K)).pointMatrix_eq_affineMatrix A
    (scalarExtensionPoint S x)
  rw [pointMatrix_baseChange, scalarExtensionPoint, MulEquiv.apply_symm_apply,
    pointMatrix_naturality, pointMatrix_eq_affineMatrix] at h
  apply Units.ext
  apply Matrix.map_injective hq
  exact (congrArg Units.val h).symm

end Tests

/-- Scalar extension preserves actual intertwiners on every affine test algebra. -/
theorem Intertwines.baseChange {ρ : MatrixRepresentation G n}
    {τ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines τ C) :
    (ρ.baseChange (algebraBaseMap k K)).Intertwines
      (τ.baseChange (algebraBaseMap k K)) (C.map (algebraMap k K)) := by
  intro A x
  let : Algebra k A := Algebra.compHom A (algebraMap k K)
  let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  let A₀ := CommAlgCat.of (CommRingCat.of k) A
  let y : G.affinePoints A₀ := (CocharacterSplitting.testIso K A).inv ≫
    baseChangePointsEquiv (algebraBaseMap k K) G _ x
  have hy : scalarExtensionPoint A y = x := by
    apply (baseChangePointsEquiv (algebraBaseMap k K) G _).injective
    simp only [scalarExtensionPoint, MulEquiv.apply_symm_apply, y,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← hy, affineMatrix_scalarExtensionPoint, affineMatrix_scalarExtensionPoint]
  have hmap : (C.map (algebraMap k K)).map (algebraMap K A) =
      C.map (algebraMap k A) := by
    ext i j
    exact (IsScalarTower.algebraMap_apply k K A (C i j)).symm
  rw [hmap]
  exact hC A₀ y

section Affine

variable [IsAffineHom G.X.hom]

/-- A constant matrix intertwines if and only if it does at the universal affine point. -/
theorem intertwines_iff_universalCharacterMatrix (ρ : MatrixRepresentation G n)
    (τ : MatrixRepresentation G m) (C : Matrix m n k) :
    ρ.Intertwines τ C ↔
      C.map (algebraMap k (CharacterUnits.Coord G)) * ρ.universalCharacterMatrix =
        τ.universalCharacterMatrix * C.map (algebraMap k (CharacterUnits.Coord G)) := by
  constructor
  · exact fun h => h _ (CharacterUnits.universalPoint G)
  · intro h A x
    let f := Lie.pointCoordinates G x
    have hρ := ρ.affineMatrix_naturality (CommAlgCat.ofHom f)
      (CharacterUnits.universalPoint G)
    have hτ := τ.affineMatrix_naturality (CommAlgCat.ofHom f)
      (CharacterUnits.universalPoint G)
    rw [← GroupScheme.affinePointMap_apply, CharacterUnits.affinePointMap_universalPoint] at hρ hτ
    rw [hρ, hτ]
    have hh := congrArg (fun M : Matrix m n (CharacterUnits.Coord G) =>
      M.map f.toRingHom) h
    have hmap : (C.map (algebraMap k (CharacterUnits.Coord G))).map f.toRingHom =
        C.map (algebraMap k A) := by
      ext i j
      exact f.commutes (C i j)
    change C.map (algebraMap k A) * ρ.universalCharacterMatrix.map f.toRingHom =
      τ.universalCharacterMatrix.map f.toRingHom * C.map (algebraMap k A)
    simpa only [Matrix.map_mul, hmap] using hh

/-- Applying an original-field linear functional to extension-field entries of an
actual intertwiner produces an actual original-field intertwiner. -/
theorem Intertwines.linearFunctional_descent {ρ : MatrixRepresentation G n}
    {τ : MatrixRepresentation G m} {C : Matrix m n K}
    (hC : (ρ.baseChange (algebraBaseMap k K)).Intertwines
      (τ.baseChange (algebraBaseMap k K)) C) (φ : K →ₗ[k] k) :
    ρ.Intertwines τ (C.map φ) := by
  let B := CharacterUnits.Coord G
  let S := K ⊗[k] B
  let A := CommAlgCat.of (CommRingCat.of K) S
  let A₀ := CommAlgCat.of (CommRingCat.of k) S
  let incR : B ⟶ A₀ := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  let y : G.affinePoints A₀ := (algSpec (CommRingCat.of k)).map incR.op ≫
    CharacterUnits.universalPoint G
  have h := hC A (scalarExtensionPoint S y)
  rw [affineMatrix_scalarExtensionPoint, affineMatrix_scalarExtensionPoint,
    affineMatrix_naturality, affineMatrix_naturality] at h
  change C.map (Algebra.TensorProduct.includeLeft : K →ₐ[k] S) *
      ρ.universalCharacterMatrix.map (Algebra.TensorProduct.includeRight : B →ₐ[k] S) =
    τ.universalCharacterMatrix.map (Algebra.TensorProduct.includeRight : B →ₐ[k] S) *
      C.map (Algebra.TensorProduct.includeLeft : K →ₐ[k] S) at h
  apply (intertwines_iff_universalCharacterMatrix ρ τ (C.map φ)).mpr
  ext i j
  have hh := congrArg (tensorCoefficient φ) (congrFun (congrFun h i) j)
  simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one, tensorCoefficient_tmul, Algebra.smul_def, mul_comm] using hh

end Affine

end Langlands.GroupScheme.MatrixRepresentation
