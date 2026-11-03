import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Langlands.GroupScheme.Rational.CharacterUnits
import Mathlib.LinearAlgebra.DFinsupp

/-! # Character spaces and coefficient projections for actual representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj Classical

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The matrix of the representation at the universal affine point. -/
def universalCharacterMatrix (ρ : MatrixRepresentation G n) :
    Matrix n n (CharacterUnits.Coord G) :=
  (ρ.affineMatrix (CharacterUnits.Coord G) (CharacterUnits.universalPoint G) :
    Matrix n n (CharacterUnits.Coord G))

/-- Scalar extension of a coordinate vector to the coordinate algebra. -/
def universalVector : (n → k) →ₗ[k] (n → CharacterUnits.Coord G) where
  toFun v := fun r => algebraMap k (CharacterUnits.Coord G) (v r)
  map_add' v w := by ext r; exact map_add _ _ _
  map_smul' c v := by
    ext r
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul, Algebra.smul_def]

/-- The universal action is linear over the original field. -/
def universalCharacterAction (ρ : MatrixRepresentation G n) :
    (n → k) →ₗ[k] (n → CharacterUnits.Coord G) where
  toFun v := ρ.universalCharacterMatrix *ᵥ universalVector v
  map_add' v w := by rw [map_add, Matrix.mulVec_add]
  map_smul' c v := by
    rw [map_smul, Matrix.mulVec_smul]
    rfl

/-- The character space is detected at the universal affine point. -/
def characterSpace (ρ : MatrixRepresentation G n) (χ : rationalCharacters G) :
    Submodule k (n → k) where
  carrier := {v | ρ.universalCharacterAction v =
    (CharacterUnits.unit χ : CharacterUnits.Coord G) • universalVector v}
  zero_mem' := by simp
  add_mem' {v w} hv hw := by
    change ρ.universalCharacterAction v = _ at hv
    change ρ.universalCharacterAction w = _ at hw
    change ρ.universalCharacterAction (v + w) = _
    simp only [map_add, hv, hw, smul_add]
  smul_mem' c v hv := by
    change ρ.universalCharacterAction v = _ at hv
    change ρ.universalCharacterAction (c • v) = _
    simp only [map_smul, hv]
    exact smul_comm _ _ _

theorem mem_characterSpace_iff (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G) (v : n → k) :
    v ∈ ρ.characterSpace χ ↔
      ρ.universalCharacterMatrix *ᵥ
          (fun r => algebraMap k (CharacterUnits.Coord G) (v r)) =
        (CharacterUnits.unit χ : CharacterUnits.Coord G) •
          (fun r => algebraMap k (CharacterUnits.Coord G) (v r)) :=
  Iff.rfl

/-- The universal character equation implies the same equation at every affine
point, including points over nonreduced algebras. -/
theorem characterSpace_affine {ρ : MatrixRepresentation G n}
    {χ : rationalCharacters G} {v : n → k} (hv : v ∈ ρ.characterSpace χ)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) :
    (ρ.affineMatrix A x : Matrix n n A) *ᵥ
        (fun r => algebraMap k A (v r)) =
      (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ χ.toMul.hom.hom) : A) •
        (fun r => algebraMap k A (v r)) := by
  let f := Lie.pointCoordinates G x
  have hmat := ρ.affineMatrix_naturality (CommAlgCat.ofHom f)
    (CharacterUnits.universalPoint G)
  rw [← GroupScheme.affinePointMap_apply, CharacterUnits.affinePointMap_universalPoint] at hmat
  rw [hmat, CharacterUnits.affineUnitsEquiv_comp]
  funext r
  have h := congrArg (fun z => f (z r)) hv
  change f.toRingHom ((ρ.universalCharacterMatrix *ᵥ
      (fun s => algebraMap k (CharacterUnits.Coord G) (v s))) r) =
    f ((CharacterUnits.unit χ : CharacterUnits.Coord G) *
      algebraMap k (CharacterUnits.Coord G) (v r)) at h
  rw [f.toRingHom.map_mulVec] at h
  change (ρ.universalCharacterMatrix.map f.toRingHom *ᵥ
      (fun s => algebraMap k A (v s))) r =
    f (CharacterUnits.unit χ) * algebraMap k A (v r)
  have hf : f.toRingHom ∘ (fun s => algebraMap k (CharacterUnits.Coord G) (v s)) =
      (fun s => algebraMap k A (v s)) := by
    funext s
    exact f.commutes (v s)
  rw [hf] at h
  simpa only [map_mul, f.commutes] using h

/-- Coordinate linear functionals separate every rational character of an affine
group, without any commutativity or smoothness assumption on the group. -/
theorem exists_characterCoefficient (χ : rationalCharacters G) :
    ∃ L : CharacterUnits.Coord G →ₗ[k] k,
      ∀ ψ : rationalCharacters G,
        L (CharacterUnits.unit ψ : CharacterUnits.Coord G) =
          if ψ = χ then 1 else 0 := by
  classical
  let F := Finsupp.linearCombination k
    (fun ψ : rationalCharacters G => (CharacterUnits.unit ψ : CharacterUnits.Coord G))
  have hF : LinearMap.ker F = ⊥ :=
    linearIndependent_iff_ker.mp (CharacterUnits.linearIndependent_unit (G := G))
  refine ⟨(Finsupp.lapply χ).comp F.leftInverse, ?_⟩
  intro ψ
  have h := LinearMap.leftInverse_apply_of_inj hF (Finsupp.single ψ (1 : k))
  have h' := congrArg (fun f : rationalCharacters G →₀ k => f χ) h
  simpa [F, Finsupp.linearCombination_single, Finsupp.single_apply, eq_comm] using h'

/-- A coefficient functional selecting one character. -/
def characterCoefficient (χ : rationalCharacters G) :
    CharacterUnits.Coord G →ₗ[k] k :=
  Classical.choose (exists_characterCoefficient χ)

theorem characterCoefficient_unit (χ ψ : rationalCharacters G) :
    characterCoefficient χ (CharacterUnits.unit ψ : CharacterUnits.Coord G) =
      if ψ = χ then 1 else 0 :=
  Classical.choose_spec (exists_characterCoefficient χ) ψ

/-- Apply the selected character coefficient to the universal action. -/
def characterProjector (ρ : MatrixRepresentation G n) (χ : rationalCharacters G) :
    (n → k) →ₗ[k] (n → k) where
  toFun v := fun r => characterCoefficient χ (ρ.universalCharacterAction v r)
  map_add' v w := by ext r; simp only [map_add, Pi.add_apply]
  map_smul' c v := by ext r; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- The coefficient projection is identity on its character space and zero on
every other character space. -/
theorem characterProjector_of_mem (ρ : MatrixRepresentation G n)
    (χ ψ : rationalCharacters G) {v : n → k} (hv : v ∈ ρ.characterSpace ψ) :
    ρ.characterProjector χ v = if ψ = χ then v else 0 := by
  classical
  funext r
  change characterCoefficient χ (ρ.universalCharacterAction v r) = _
  rw [show ρ.universalCharacterAction v =
    (CharacterUnits.unit ψ : CharacterUnits.Coord G) • universalVector v from hv]
  change characterCoefficient χ
    ((CharacterUnits.unit ψ : CharacterUnits.Coord G) *
      algebraMap k (CharacterUnits.Coord G) (v r)) = _
  rw [mul_comm, ← Algebra.smul_def]
  rw [map_smul, characterCoefficient_unit]
  split_ifs <;> simp_all

/-- The character spaces of an actual representation of an arbitrary affine
group scheme over a field are independent. -/
theorem characterSpace_iSupIndep (ρ : MatrixRepresentation G n) :
    iSupIndep ρ.characterSpace := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro t v hv hsum χ hχ
  have h := congrArg (ρ.characterProjector χ) hsum
  simp only [map_sum, map_zero] at h
  have he : (∑ ψ ∈ t, ρ.characterProjector χ (v ψ)) = v χ := by
    calc
      (∑ ψ ∈ t, ρ.characterProjector χ (v ψ)) =
          ∑ ψ ∈ t, if ψ = χ then v ψ else 0 := by
        apply Finset.sum_congr rfl
        intro ψ hψ
        exact characterProjector_of_mem ρ χ ψ (hv ψ hψ)
      _ = v χ := by simp [hχ]
  exact he.symm.trans h

end Langlands.GroupScheme.MatrixRepresentation
