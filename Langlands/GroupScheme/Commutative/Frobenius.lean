import Langlands.GroupScheme.Rational.AffineCommutatorCoordinates
import Langlands.GroupScheme.Rational.UnipotentPointsExponent
import Langlands.GroupScheme.Rational.TorusUnipotence.MatrixCoefficients
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Frobenius powers on commutative affine groups -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.CommutativeFrobenius

section Matrices

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [Algebra k B]
    {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The finite union of the basis supports of all entries of a matrix. -/
def coefficientSupport {idx : Type*} (b : Module.Basis idx k B)
    (M : Matrix n n B) : Finset idx := by
  classical
  exact Finset.univ.biUnion fun i : n =>
    Finset.univ.biUnion fun j : n => (b.repr (M i j)).support

omit [DecidableEq n] in
theorem support_subset_coefficientSupport {idx : Type*} (b : Module.Basis idx k B)
    (M : Matrix n n B) (i j : n) :
    (b.repr (M i j)).support ⊆ coefficientSupport b M := by
  classical
  intro t ht
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr
    ⟨j, Finset.mem_univ _, ht⟩⟩

omit [DecidableEq n] in
/-- Extracting two scalar coefficients of a universally commuting matrix gives
commuting matrices over the ground field. -/
theorem coefficient_matrices_commute (M : Matrix n n B)
    (hM : Commute
      (M.map (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B))
      (M.map (Algebra.TensorProduct.includeRight : B →ₐ[k] B ⊗[k] B)))
    (f g : B →ₗ[k] k) : Commute (M.map f) (M.map g) := by
  let e : B ⊗[k] B →ₗ[k] k :=
    (TensorProduct.lid k k).toLinearMap ∘ₗ TensorProduct.map f g
  have he (x y : B) : e (x ⊗ₜ[k] y) = f x * g y := by
    simp [e]
  show (M.map f) * (M.map g) = (M.map g) * (M.map f)
  ext i j
  have h := congrArg e (congrArg (fun X : Matrix n n (B ⊗[k] B) => X i j) hM.eq)
  simp only [Matrix.mul_apply, Matrix.map_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, map_sum, he] at h
  simpa only [Matrix.mul_apply, Matrix.map_apply, mul_comm] using h

/-- The characteristic-power identity for a finite family of pairwise commuting
elements of a possibly noncommutative semiring. -/
theorem sum_pow_expChar_pow {R : Type*} [Semiring R] (p e : ℕ) [ExpChar R p]
    {idx : Type*} (s : Finset idx) (a : idx → R)
    (ha : ∀ i ∈ s, ∀ j ∈ s, Commute (a i) (a j)) :
    (∑ i ∈ s, a i) ^ p ^ e = ∑ i ∈ s, a i ^ p ^ e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact zero_pow (pow_ne_zero e (expChar_ne_zero R p))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      add_pow_expChar_pow_of_commute p e
        (Commute.sum_right s a (a i) (fun j hj => ha i (by simp) j (by simp [hj])))]
    rw [ih (fun j hj l hl => ha j (by simp [hj]) l (by simp [hl]))]

omit [Fintype n] [DecidableEq n] in
/-- A finite set covering the basis supports of the entries gives a common
coefficient expansion for the whole matrix after any scalar evaluation. -/
theorem matrix_map_eq_sum_coefficients {idx : Type*} (b : Module.Basis idx k B)
    (M : Matrix n n B) (s : Finset idx)
    (hs : ∀ i j, (b.repr (M i j)).support ⊆ s)
    {A : Type*} [CommRing A] [Algebra k A] (f : B →ₐ[k] A) :
    M.map f =
      ∑ t ∈ s, f (b t) • (M.map (b.coord t)).map (algebraMap k A) := by
  classical
  ext i j
  have h : ∑ t ∈ s, b.repr (M i j) t • b t = M i j := by
    rw [← Finsupp.linearCombination_apply_of_mem_supported (R := k)
      (show b.repr (M i j) ∈ Finsupp.supported k k (↑s : Set idx) from hs i j)]
    exact b.linearCombination_repr _
  have hf := congrArg f h
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    Module.Basis.coord_apply]
  simpa only [map_sum, Algebra.smul_def, map_mul, AlgHom.commutes,
    Algebra.algebraMap_self_apply, mul_comm] using hf.symm

/-- For a universally commuting matrix, characteristic powers of scalar
evaluations depend only on the same powers of the evaluated scalars. -/
theorem matrix_map_pow_eq (M : Matrix n n B)
    (hM : Commute
      (M.map (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B))
      (M.map (Algebra.TensorProduct.includeRight : B →ₐ[k] B ⊗[k] B)))
    {A : Type*} [CommRing A] [Algebra k A] (p e : ℕ) [ExpChar k p]
    (f g : B →ₐ[k] A) (hfg : ∀ b, f b ^ p ^ e = g b ^ p ^ e) :
    (M.map f) ^ p ^ e = (M.map g) ^ p ^ e := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  cases isEmpty_or_nonempty n with
  | inl hn => exact Subsingleton.elim _ _
  | inr hn =>
    have : ExpChar (Matrix n n A) p :=
      expChar_of_injective_algebraMap (algebraMap k (Matrix n n A)).injective p
    let b := Module.Free.chooseBasis k B
    let s := coefficientSupport b M
    have hs (i j : n) : (b.repr (M i j)).support ⊆ s :=
      support_subset_coefficientSupport b M i j
    let C := fun t => (M.map (b.coord t)).map (algebraMap k A)
    have hC (i j) : Commute (C i) (C j) :=
      (coefficient_matrices_commute M hM (b.coord i) (b.coord j)).map
        (algebraMap k A).mapMatrix
    have hterms (h : B →ₐ[k] A) (i j) :
        Commute (h (b i) • C i) (h (b j) • C j) := by
      show (h (b i) • C i) * (h (b j) • C j) =
        (h (b j) • C j) * (h (b i) • C i)
      rw [smul_mul_smul_comm, smul_mul_smul_comm, (hC i j).eq, mul_comm]
    rw [matrix_map_eq_sum_coefficients b M s hs f,
      matrix_map_eq_sum_coefficients b M s hs g]
    rw [sum_pow_expChar_pow p e s _ (fun i _ j _ => hterms f i j),
      sum_pow_expChar_pow p e s _ (fun i _ j _ => hterms g i j)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [smul_pow, smul_pow, hfg]

end Matrices

section GroupPoints

open TorusUnipotence

variable {k : Type u} [Field k] (Z : CommGroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom Z.toGrp.X.hom]

/-- The two independent tensor evaluations of a commutative group's universal
representation matrix commute. -/
theorem coeffMatrix_tensor_commute {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation Z.toGrp n) :
    Commute
      ((coeffMatrix ρ).map (Algebra.TensorProduct.includeLeft :
        CharacterUnits.Coord Z.toGrp →ₐ[k]
          CharacterUnits.Coord Z.toGrp ⊗[k] CharacterUnits.Coord Z.toGrp))
      ((coeffMatrix ρ).map (Algebra.TensorProduct.includeRight :
        CharacterUnits.Coord Z.toGrp →ₐ[k]
          CharacterUnits.Coord Z.toGrp ⊗[k] CharacterUnits.Coord Z.toGrp)) := by
  let A := CharacterUnits.Coord Z.toGrp ⊗[k] CharacterUnits.Coord Z.toGrp
  let x : Lie.AffinePoints Z.toGrp A := pt Z.toGrp Algebra.TensorProduct.includeLeft
  let y : Lie.AffinePoints Z.toGrp A := pt Z.toGrp Algebra.TensorProduct.includeRight
  have h := congrArg (fun z : Lie.AffinePoints Z.toGrp A =>
    (ρ.affineMatrix (CommAlgCat.of _ A) z : Matrix n n A)) (mul_comm x y)
  dsimp only [x, y, A] at h
  show _ * _ = _ * _
  simp only [map_mul, Units.val_mul] at h
  rw [affineMatrix_pt ρ (Algebra.TensorProduct.includeLeft :
      CharacterUnits.Coord Z.toGrp →ₐ[k] A),
    affineMatrix_pt ρ (Algebra.TensorProduct.includeRight :
      CharacterUnits.Coord Z.toGrp →ₐ[k] A)] at h
  exact h

/-- A coefficient endomorphism preserving all characteristic powers also
preserves those powers on points of a finite type commutative affine group. -/
theorem affinePoints_pow_eq [LocallyOfFiniteType Z.toGrp.X.hom]
    (p e : ℕ) [ExpChar k p] {A : Type u} [CommRing A] [Algebra k A]
    (g : A →ₐ[k] A) (hg : ∀ a : A, a ^ p ^ e = g a ^ p ^ e)
    (x : Lie.AffinePoints Z.toGrp A) :
    x ^ p ^ e = Lie.affineMap Z.toGrp g x ^ p ^ e := by
  obtain ⟨N, ρ, hρ⟩ :=
    affineLinearEmbeddingStatement k Z.toGrp inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono ρ.hom.hom).1
  apply (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
    (CommAlgCat.of _ A)).injective
  change ρ.affineMatrix _ (x ^ p ^ e) =
    ρ.affineMatrix _ (Lie.affineMap Z.toGrp g x ^ p ^ e)
  rw [map_pow, map_pow]
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val]
  have hmatrix (y : Lie.AffinePoints Z.toGrp A) :
      (ρ.affineMatrix (CommAlgCat.of _ A) y : Matrix (Fin N) (Fin N) A) =
        (coeffMatrix ρ).map (Lie.pointCoordinates Z.toGrp y) := by
    simpa only [pt, Equiv.symm_apply_apply] using
      affineMatrix_pt ρ (Lie.pointCoordinates Z.toGrp y)
  rw [hmatrix, hmatrix, Lie.pointCoordinates_naturality]
  exact matrix_map_pow_eq (coeffMatrix ρ) (coeffMatrix_tensor_commute Z ρ)
    p e _ _ (fun b => hg (Lie.pointCoordinates Z.toGrp x b))

end GroupPoints

end Langlands.GroupScheme.CommutativeFrobenius
