import Langlands.GroupScheme.Rational.WeightShiftingTangent

/-! # Faithful tangent maps reflect adjoint weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G) {n : ℕ}

local instance : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom

/-- The tangent image intersected with the degree-`chi` endomorphisms. -/
def representationTangentWeightSpace (r : MatrixRepresentation G (Fin n))
    (chi : characterLattice p.torus) : Submodule k (Module.End k (Fin n → k)) :=
  LinearMap.range (Matrix.toLin'.toLinearMap.comp (r.kernelDifferential k)) ⊓
    p.representationWeightShift r chi

/-- Every weight-shifting endomorphism satisfies its all-algebra torus intertwining identity. -/
theorem matrix_weightShift_comm
    (r : MatrixRepresentation G (Fin n)) (chi : characterLattice p.torus)
    (B : Matrix (Fin n) (Fin n) k)
    (hB : Matrix.toLin' B ∈ p.representationWeightShift r chi)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (t : GroupScheme.affinePoints p.torus.toGrp A) :
    (r.affineMatrix A (t ≫ p.inclusion.hom.hom) : Matrix (Fin n) (Fin n) A) *
        B.map (algebraMap k A) =
      (Lie.characterValue chi t : A) • B.map (algebraMap k A) *
        (r.affineMatrix A (t ≫ p.inclusion.hom.hom) : Matrix (Fin n) (Fin n) A) := by
  classical
  let g := r.affineMatrix A (t ≫ p.inclusion.hom.hom)
  let M := B.map (algebraMap k A)
  let vmap : (Fin n → k) →ₗ[k] (Fin n → A) :=
    { toFun := fun v i => algebraMap k A (v i)
      map_add' := fun v w => by ext i; exact map_add _ _ _
      map_smul' := fun c v => by
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul, Algebra.smul_def] }
  let act (D : Matrix (Fin n) (Fin n) A) : (Fin n → k) →ₗ[k] (Fin n → A) :=
    ((Matrix.toLin' D).restrictScalars k).comp vmap
  have hlin : act ((g : Matrix (Fin n) (Fin n) A) * M) =
      act ((Lie.characterValue chi t : A) • (M * (g : Matrix (Fin n) (Fin n) A))) := by
    have hker : (⨆ mu, p.representationWeightSpace r mu) ≤
        LinearMap.ker (act ((g : Matrix (Fin n) (Fin n) A) * M) -
          act ((Lie.characterValue chi t : A) • (M * (g : Matrix (Fin n) (Fin n) A)))) := by
      apply iSup_le
      intro mu v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      have hvA : (g : Matrix (Fin n) (Fin n) A) *ᵥ vmap v =
          (Lie.characterValue mu t : A) • vmap v :=
        MatrixRepresentation.characterSpace_affine hv A t
      have hwA : (g : Matrix (Fin n) (Fin n) A) *ᵥ vmap (B *ᵥ v) =
          (Lie.characterValue (mu + chi) t : A) • vmap (B *ᵥ v) :=
        MatrixRepresentation.characterSpace_affine (hB mu v hv) A t
      have hw : vmap (B *ᵥ v) = M *ᵥ vmap v := by
        ext i
        exact (algebraMap k A).map_mulVec _ _ i
      rw [hw] at hwA
      have hadd : Lie.characterValue (mu + chi) t =
          Lie.characterValue mu t * Lie.characterValue chi t := by
        unfold Lie.characterValue
        rw [comp_groupHom_add, map_mul]
      change ((g : Matrix (Fin n) (Fin n) A) * M) *ᵥ vmap v =
        ((Lie.characterValue chi t : A) • (M * (g : Matrix (Fin n) (Fin n) A))) *ᵥ vmap v
      rw [← Matrix.mulVec_mulVec, hwA, Matrix.smul_mulVec,
        ← Matrix.mulVec_mulVec, hvA, Matrix.mulVec_smul, smul_smul, hadd, Units.val_mul,
        mul_comm]
    rw [p.iSup_representationWeightSpace_eq_top] at hker
    exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp (top_le_iff.mp hker))
  have hmat : (g : Matrix (Fin n) (Fin n) A) * M =
      (Lie.characterValue chi t : A) • (M * (g : Matrix (Fin n) (Fin n) A)) := by
    ext i j
    have h := congrArg (fun f : (Fin n → k) →ₗ[k] (Fin n → A) => f (Pi.single j 1) i) hlin
    simpa [act, vmap, Matrix.toLin'_apply, Matrix.mulVec, Matrix.mul_apply, dotProduct, Pi.single_apply] using h
  simpa only [smul_mul_assoc] using hmat

/-- If the representation is monomorphic, a weight-shifting tangent operator comes from
that actual adjoint weight space. -/
theorem mem_weightSpace_of_kernelDifferential_mem_representationWeightShift
    (r : MatrixRepresentation G (Fin n)) (hr : Mono r.hom.hom)
    (chi : characterLattice p.torus) (X : Additive (lieKernel G k))
    (hX : Matrix.toLin' (r.kernelDifferential k X) ∈ p.representationWeightShift r chi) :
    X ∈ weightSpace p.inclusion chi := by
  intro A _ _ t
  have hinj : Function.Injective (r.kernelDifferential A) := by
    intro Y Z h
    apply Additive.toMul.injective
    exact r.tangentMatrix_injective hr A h
  apply hinj
  simp only [map_smul, MatrixRepresentation.kernelDifferential_apply, adjoint_toMul,
    lieKernelMapLinear_toMul, r.tangentMatrix_conjugation, r.tangentMatrix_naturality]
  change (r.affineMatrix (CommAlgCat.of k A) (t ≫ p.inclusion.hom.hom) :
      Matrix (Fin n) (Fin n) A) * (r.kernelDifferential k X).map (algebraMap k A) *
      ((r.affineMatrix (CommAlgCat.of k A) (t ≫ p.inclusion.hom.hom))⁻¹ : GL (Fin n) A) =
    (Lie.characterValue chi t : A) • (r.kernelDifferential k X).map (algebraMap k A)
  rw [p.matrix_weightShift_comm r chi _ hX (CommAlgCat.of k A) t, mul_assoc,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

/-- A faithful tangent map identifies adjoint degree with representation weight shift. -/
theorem kernelDifferential_mem_representationWeightShift_iff
    (r : MatrixRepresentation G (Fin n)) (hr : Mono r.hom.hom)
    (chi : characterLattice p.torus) (X : Additive (lieKernel G k)) :
    Matrix.toLin' (r.kernelDifferential k X) ∈ p.representationWeightShift r chi ↔
      X ∈ weightSpace p.inclusion chi :=
  ⟨p.mem_weightSpace_of_kernelDifferential_mem_representationWeightShift r hr chi X,
    p.toLin_kernelDifferential_mem_representationWeightShift r⟩

end Langlands.GroupScheme.SplitPinning
