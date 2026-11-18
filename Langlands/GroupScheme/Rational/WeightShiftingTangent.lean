import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.Lie.PrimePowerFieldExtension
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Lie.Functoriality

/-! # Adjoint weights and weight-shifting tangent operators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The all-algebra character equation also suffices for membership in the actual
character space, by specializing to its universal affine point. -/
theorem mem_characterSpace_of_forall_affine
    (r : MatrixRepresentation G n) (chi : rationalCharacters G) (v : n → k)
    (h : ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A),
      (r.affineMatrix A x : Matrix n n A) *ᵥ (fun i => algebraMap k A (v i)) =
        (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ chi.toMul.hom.hom) : A) •
          (fun i => algebraMap k A (v i))) :
    v ∈ r.characterSpace chi :=
  h (CommAlgCat.of k (CharacterUnits.Coord G)) (CharacterUnits.universalPoint G)

end MatrixRepresentation

namespace SplitPinning

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G) {n : ℕ}

local instance : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom

/-- The endomorphisms of a representation that shift each torus weight by `chi`. -/
def representationWeightShift (r : MatrixRepresentation G (Fin n))
    (chi : characterLattice p.torus) : Submodule k (Module.End k (Fin n → k)) where
  carrier := {f | ∀ mu, ∀ v ∈ p.representationWeightSpace r mu,
    f v ∈ p.representationWeightSpace r (mu + chi)}
  zero_mem' := by intro mu v _; exact Submodule.zero_mem _
  add_mem' := by intro f g hf hg mu v hv; exact Submodule.add_mem _ (hf mu v hv) (hg mu v hv)
  smul_mem' := by intro c f hf mu v hv; exact Submodule.smul_mem _ c (hf mu v hv)

/-- The tangent matrix of an actual adjoint-weight vector intertwines the torus matrices
with the scalar given by that character, over every coefficient algebra. -/
theorem tangentMatrix_weight_comm (r : MatrixRepresentation G (Fin n))
    {chi : characterLattice p.torus} {X : Additive (lieKernel G k)}
    (hX : X ∈ weightSpace p.inclusion chi)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (t : GroupScheme.affinePoints p.torus.toGrp A) :
    (r.affineMatrix A (t ≫ p.inclusion.hom.hom) : Matrix (Fin n) (Fin n) A) *
        (r.kernelDifferential k X).map (algebraMap k A) =
      (Lie.characterValue chi t : A) • (r.kernelDifferential k X).map (algebraMap k A) *
        (r.affineMatrix A (t ≫ p.inclusion.hom.hom) : Matrix (Fin n) (Fin n) A) := by
  have h := congrArg (r.kernelDifferential A) (hX A t)
  simp only [map_smul, MatrixRepresentation.kernelDifferential_apply, adjoint_toMul,
    lieKernelMapLinear_toMul, r.tangentMatrix_conjugation, r.tangentMatrix_naturality] at h
  change (r.affineMatrix A (t ≫ p.inclusion.hom.hom) : Matrix (Fin n) (Fin n) A) *
      (r.kernelDifferential k X).map (algebraMap k A) *
        ((r.affineMatrix A (t ≫ p.inclusion.hom.hom))⁻¹ : GL (Fin n) A) =
    (Lie.characterValue chi t : A) • (r.kernelDifferential k X).map (algebraMap k A) at h
  have hm := congrArg (fun B : Matrix (Fin n) (Fin n) A =>
    B * (r.affineMatrix A (t ≫ p.inclusion.hom.hom) : Matrix (Fin n) (Fin n) A)) h
  simpa only [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one,
    smul_mul_assoc, MatrixRepresentation.kernelDifferential_apply, Algebra.ofId_apply] using hm

/-- A tangent vector of adjoint weight `chi` sends every representation weight `mu`
into weight `mu + chi`. -/
theorem tangentMatrix_mulVec_mem_representationWeightSpace
    (r : MatrixRepresentation G (Fin n))
    {chi : characterLattice p.torus} {X : Additive (lieKernel G k)}
    (hX : X ∈ weightSpace p.inclusion chi) (mu : characterLattice p.torus)
    {v : Fin n → k} (hv : v ∈ p.representationWeightSpace r mu) :
    r.kernelDifferential k X *ᵥ v ∈ p.representationWeightSpace r (mu + chi) := by
  apply MatrixRepresentation.mem_characterSpace_of_forall_affine
  intro A t
  let M := (r.kernelDifferential k X).map (algebraMap k A)
  let g := r.affineMatrix A (t ≫ p.inclusion.hom.hom)
  let vA : Fin n → A := fun i => algebraMap k A (v i)
  have hvA : (g : Matrix (Fin n) (Fin n) A) *ᵥ vA =
      (Lie.characterValue mu t : A) • vA :=
    MatrixRepresentation.characterSpace_affine hv A t
  have hw : (fun i => algebraMap k A ((r.kernelDifferential k X *ᵥ v) i)) = M *ᵥ vA := by
    ext i
    exact (algebraMap k A).map_mulVec _ _ i
  rw [hw]
  change (g : Matrix (Fin n) (Fin n) A) *ᵥ (M *ᵥ vA) =
    (Lie.characterValue (mu + chi) t : A) • (M *ᵥ vA)
  have hadd : Lie.characterValue (mu + chi) t =
      Lie.characterValue mu t * Lie.characterValue chi t := by
    unfold Lie.characterValue
    rw [comp_groupHom_add, map_mul]
  rw [hadd, Units.val_mul, Matrix.mulVec_mulVec, p.tangentMatrix_weight_comm r hX A t,
    ← Matrix.mulVec_mulVec, hvA, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_comm]

/-- The tangent image of an adjoint-weight vector belongs to the corresponding
weight-shifting subspace of endomorphisms. -/
theorem toLin_kernelDifferential_mem_representationWeightShift
    (r : MatrixRepresentation G (Fin n))
    {chi : characterLattice p.torus} {X : Additive (lieKernel G k)}
    (hX : X ∈ weightSpace p.inclusion chi) :
    Matrix.toLin' (r.kernelDifferential k X) ∈ p.representationWeightShift r chi :=
  p.tangentMatrix_mulVec_mem_representationWeightSpace r hX

end SplitPinning
end Langlands.GroupScheme
