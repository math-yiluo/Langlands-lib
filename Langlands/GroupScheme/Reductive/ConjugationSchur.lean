import Langlands.GroupScheme.Reductive.RegularConjugationReduction
import Langlands.GroupScheme.Reductive.InvariantLinearForm
import Mathlib.RepresentationTheory.Irreducible

/-! # Scalar values of fixed vectors in irreducible conjugation representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MatrixLinear

variable {k : Type u} [CommRing k]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Evaluating at a scalar-extended vector is entrywise scalar extension. -/
theorem eval_map (c : n → Matrix m m k) {A : Type*} [CommRing A]
    (f : k →+* A) (v : n → k) :
    eval c f (fun i => f (v i)) = (eval c (RingHom.id k) v).map f := by
  ext i j
  simp [eval]

end MatrixLinear

namespace MatrixRepresentation

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A matrix commuting with the rational action gives an actual intertwining
endomorphism of the rational-point representation. -/
def rationalIntertwiningEndomorphism (σ : MatrixRepresentation G m) (A : Matrix m m k)
    (hA : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      A * (σ.rationalMatrix g : Matrix m m k) =
        (σ.rationalMatrix g : Matrix m m k) * A) :
    Representation.IntertwiningMap σ.rationalRepresentation σ.rationalRepresentation :=
  (Matrix.toLin' A).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      change A *ᵥ ((σ.rationalMatrix g : Matrix m m k) *ᵥ v) =
        (σ.rationalMatrix g : Matrix m m k) *ᵥ (A *ᵥ v)
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA g])

/-- Schur's lemma in matrix coordinates for an actual irreducible representation. -/
theorem eq_smul_one_of_commutes (σ : MatrixRepresentation G m)
    (hσ : σ.rationalRepresentation.IsIrreducible) (A : Matrix m m k)
    (hA : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      A * (σ.rationalMatrix g : Matrix m m k) =
        (σ.rationalMatrix g : Matrix m m k) * A) :
    ∃ a : k, A = a • (1 : Matrix m m k) := by
  let := hσ
  let F := rationalIntertwiningEndomorphism σ A hA
  obtain ⟨a, ha⟩ :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := σ.rationalRepresentation) |>.surjective F
  refine ⟨a, Matrix.toLin'.injective ?_⟩
  have he := congrArg Representation.IntertwiningMap.toLinearMap ha
  change a • (LinearMap.id : (m → k) →ₗ[k] (m → k)) = Matrix.toLin' A at he
  simpa only [map_smul, Matrix.toLin'_one] using he.symm

namespace ConjugationLinearMap

variable {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}

omit [IsAlgClosed k] in
/-- The image of an all-test fixed vector commutes with every rational matrix. -/
theorem eval_fixed_commutes (φ : ConjugationLinearMap ρ σ)
    (v : n → k) (hv : ρ.IsFixedVector v)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    MatrixLinear.eval φ.coeff (RingHom.id k) v *
        (σ.rationalMatrix g : Matrix m m k) =
      (σ.rationalMatrix g : Matrix m m k) *
        MatrixLinear.eval φ.coeff (RingHom.id k) v := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have h := φ.equivariant T g (fun i => scalarMap T (v i))
  rw [hv T g, MatrixLinear.eval_map] at h
  have he := congrArg (fun M : Matrix m m Γ(T.left, ⊤) => M.map e.toRingHom) h
  have hA : ((MatrixLinear.eval φ.coeff (RingHom.id k) v).map (scalarMap T)).map
      e.toRingHom = MatrixLinear.eval φ.coeff (RingHom.id k) v := by
    ext i j
    exact e.apply_symm_apply _
  have hM : (σ.pointMatrix T g).val.map e.toRingHom =
      (σ.rationalMatrix g : Matrix m m k) := rfl
  have hMinv : ((σ.pointMatrix T g)⁻¹).val.map e.toRingHom =
      ((σ.rationalMatrix g)⁻¹).val := rfl
  simp only [Matrix.map_mul, hA, hM, hMinv] at he
  have he' := congrArg (fun M : Matrix m m k => M * (σ.rationalMatrix g).val) he
  simpa only [Matrix.mul_assoc, Units.inv_mul,
    Matrix.mul_one] using he'

/-- A fixed vector with nonzero image has a nonzero scalar-identity image when
    the actual auxiliary representation is irreducible. -/
theorem exists_nonzero_scalar_of_eval_ne_zero (φ : ConjugationLinearMap ρ σ)
    (hσ : σ.rationalRepresentation.IsIrreducible)
    (v : n → k) (hv : ρ.IsFixedVector v)
    (hne : MatrixLinear.eval φ.coeff (RingHom.id k) v ≠ 0) :
    ∃ a : k, a ≠ 0 ∧ MatrixLinear.eval φ.coeff (RingHom.id k) v =
      a • (1 : Matrix m m k) := by
  obtain ⟨a, ha⟩ := eq_smul_one_of_commutes σ hσ _ (φ.eval_fixed_commutes v hv)
  refine ⟨a, ?_, ha⟩
  intro hzero
  exact hne (by simpa [hzero] using ha)

end ConjugationLinearMap
end MatrixRepresentation

end Langlands.GroupScheme
