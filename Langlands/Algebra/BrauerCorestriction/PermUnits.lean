import Langlands.Algebra.CentralSimpleScalarExtension
import Langlands.Algebra.BrauerCorestriction.PiMatrixKronecker
import Langlands.Algebra.CentralSimple.FiniteGaloisSplitting
import Langlands.Algebra.MatrixAlgEquivInnerProof

/-!
# Permutation units in tensor powers of central simple algebras

For a finite-dimensional central simple `K`-algebra `B` and a finite type `E`, every
permutation of the tensor factors of `C = ⨂_K σ : E, B` is an inner automorphism, and the
implementing units can be chosen to form a group homomorphism `Perm E →* Cˣ`. The units are
the permutation matrices of a split model, descended from a finite Galois splitting field.
-/

universe u v w

open TensorProduct PiTensorProduct Module
open Langlands.PiTensorSemilinear Langlands.CentralSimple

namespace Langlands.BrauerCorestriction

section Perm

variable (K : Type u) [Field K] (E : Type w) (B : Type v) [Ring B] [Algebra K B]

/-- Permutation of the tensor factors of `⨂_K σ : E, B`, as a `K`-algebra automorphism. -/
noncomputable def permAlgEquiv (π : Equiv.Perm E) :
    (⨂[K] _ : E, B) ≃ₐ[K] (⨂[K] _ : E, B) :=
  AlgEquiv.ofLinearEquiv (reindex K (fun _ : E => B) π) (reindex_one K π) (reindex_mul K π)

theorem permAlgEquiv_tprod (π : Equiv.Perm E) (b : E → B) :
    permAlgEquiv K E B π (PiTensorProduct.tprod K b) =
      PiTensorProduct.tprod K (fun σ => b (π.symm σ)) := by
  rw [permAlgEquiv, AlgEquiv.ofLinearEquiv_apply, reindex_tprod]

theorem finrank_piTensor_const [Fintype E] [FiniteDimensional K B] :
    finrank K (⨂[K] _ : E, B) = finrank K B ^ Fintype.card E := by
  classical
  let b : E → Basis (Fin (finrank K B)) K B := fun _ => Module.finBasis K B
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct b), Fintype.card_pi]
  simp

end Perm

section Split

variable (K : Type u) [Field K] (B : Type u) [Ring B] [Algebra K B] [FiniteDimensional K B]
  [Algebra.IsCentral K B] [IsSimpleRing B]
variable (E : Type w) [Fintype E] [DecidableEq E]

/-- The chosen finite Galois splitting field of `B`. -/
abbrev SF : Type u := finiteGaloisSplittingField K B

/-- Matrices of the size of the splitting chart. -/
abbrev MatB : Type u :=
  Matrix (Fin (reducedDegree K B)) (Fin (reducedDegree K B)) (SF K B)

/-- Matrices indexed by functions `E → Fin d`. -/
abbrev MatE : Type (max u w) :=
  Matrix (E → Fin (reducedDegree K B)) (E → Fin (reducedDegree K B)) (SF K B)

/-- The `K`-linear map `B → M_d(SF)`, `b ↦ χ (1 ⊗ b)`, through the splitting chart. -/
noncomputable def chartLin :
    B →ₗ[K] Matrix (Fin (reducedDegree K B)) (Fin (reducedDegree K B)) (SF K B) :=
  ((finiteGaloisSplittingChart K B).toAlgHom.restrictScalars K).toLinearMap ∘ₗ
    (Algebra.TensorProduct.includeRight : B →ₐ[K] SF K B ⊗[K] B).toLinearMap

theorem chartLin_apply (b : B) :
    chartLin K B b = finiteGaloisSplittingChart K B (1 ⊗ₜ b) := rfl

theorem chartLin_one : chartLin K B 1 = 1 := by
  rw [chartLin_apply, ← Algebra.TensorProduct.one_def, map_one]

theorem chartLin_mul (x y : B) : chartLin K B (x * y) = chartLin K B x * chartLin K B y := by
  rw [chartLin_apply, chartLin_apply, chartLin_apply, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The split representation `⨂_K B → M_{E → Fin d}(SF)`, `⨂ b_σ ↦ Kronecker (χ (1 ⊗ b_σ))`. -/
noncomputable def splitRep :
    (⨂[K] _ : E, B) →ₐ[K]
      Matrix (E → Fin (reducedDegree K B)) (E → Fin (reducedDegree K B)) (SF K B) :=
  liftAlgHom (((kroneckerMultilinear (SF K B) E (reducedDegree K B)).restrictScalars K).compLinearMap
      (fun _ => chartLin K B))
    (by
      simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars,
        Pi.one_apply, chartLin_one]
      exact kroneckerMultilinear_one _ _ _)
    (fun x y => by
      simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars,
        Pi.mul_apply, chartLin_mul]
      exact kroneckerMultilinear_mul _ _ _ (fun σ => chartLin K B (x σ))
        (fun σ => chartLin K B (y σ)))

theorem splitRep_tprod (b : E → B) :
    splitRep K B E (PiTensorProduct.tprod K b) =
      kroneckerMultilinear (SF K B) E (reducedDegree K B) (fun σ => chartLin K B (b σ)) := by
  simp [splitRep]

/-- The split model `SF ⊗_K (⨂_K B) → M_{E → Fin d}(SF)`. -/
noncomputable def splitTheta :
    SF K B ⊗[K] (⨂[K] _ : E, B) →ₐ[SF K B]
      Matrix (E → Fin (reducedDegree K B)) (E → Fin (reducedDegree K B)) (SF K B) :=
  Algebra.TensorProduct.lift (Algebra.ofId (SF K B) _) (splitRep K B E)
    (fun x y => show Commute (Algebra.ofId (SF K B) _ x) (splitRep K B E y) from
      Algebra.commutes x _)

theorem splitTheta_tmul (x : SF K B) (c : ⨂[K] _ : E, B) :
    splitTheta K B E (x ⊗ₜ c) = x • splitRep K B E c := by
  rw [splitTheta, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]

end Split

section Model

variable (K : Type u) [Field K] (B : Type u) [Ring B] [Algebra K B] [FiniteDimensional K B]
  [Algebra.IsCentral K B] [IsSimpleRing B]
variable (E : Type w) [Fintype E] [DecidableEq E]

theorem splitTheta_bijective : Function.Bijective (splitTheta K B E) := by
  obtain ⟨hc, hs⟩ := piTensor_isCentral_isSimpleRing K (fun _ : E => B)
  have : FiniteDimensional K (⨂[K] _ : E, B) := PiTensorProduct.finite
  have : IsSimpleRing (SF K B ⊗[K] (⨂[K] _ : E, B)) :=
    isSimpleRing_baseChange K (⨂[K] _ : E, B) (SF K B)
  have : Nonempty (E → Fin (reducedDegree K B)) :=
    ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  have hinj : Function.Injective (splitTheta K B E) := by
    rcases IsSimpleRing.injective_ringHom_or_subsingleton_codomain
      (R := SF K B ⊗[K] (⨂[K] _ : E, B))
      (S := Matrix (E → Fin (reducedDegree K B)) (E → Fin (reducedDegree K B)) (SF K B))
      (splitTheta K B E).toRingHom with h | h
    · exact h
    · exact absurd h (not_subsingleton _)
  refine ⟨hinj, ?_⟩
  have hd : finrank (SF K B) (SF K B ⊗[K] (⨂[K] _ : E, B)) =
      finrank (SF K B)
        (Matrix (E → Fin (reducedDegree K B)) (E → Fin (reducedDegree K B)) (SF K B)) := by
    rw [Module.finrank_baseChange, finrank_piTensor_const, (finiteGaloisSplittingChart_spec K B).2,
      Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fun, Fintype.card_fin,
      mul_pow]
  have key := LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := SF K B)
    (V := SF K B ⊗[K] (⨂[K] _ : E, B))
    (V₂ := Matrix (E → Fin (reducedDegree K B)) (E → Fin (reducedDegree K B)) (SF K B))
    (f := { toFun := splitTheta K B E
            map_add' := map_add _
            map_smul' := fun c x => map_smul (splitTheta K B E) c x }) hd
  exact key.mp hinj

/-- The split model as an `SF`-algebra isomorphism. -/
noncomputable def splitThetaEquiv :
    SF K B ⊗[K] (⨂[K] _ : E, B) ≃ₐ[SF K B]
      Matrix (E → Fin (reducedDegree K B)) (E → Fin (reducedDegree K B)) (SF K B) :=
  AlgEquiv.ofBijective (splitTheta K B E) (splitTheta_bijective K B E)

theorem splitThetaEquiv_apply (z : SF K B ⊗[K] (⨂[K] _ : E, B)) :
    splitThetaEquiv K B E z = splitTheta K B E z := rfl

/-- Under the split model, permuting tensor factors is reindexing rows and columns. -/
theorem splitRep_perm (π : Equiv.Perm E) (c : ⨂[K] _ : E, B) :
    splitRep K B E (permAlgEquiv K E B π c) =
      (splitRep K B E c).submatrix (indexPerm π).symm (indexPerm π).symm := by
  induction c using PiTensorProduct.induction_on with
  | smul_tprod r b =>
    rw [map_smul, map_smul, map_smul, permAlgEquiv_tprod, splitRep_tprod, splitRep_tprod,
      kroneckerMultilinear_reindex π (fun σ => chartLin K B (b σ))]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    rfl

/-- The permutation matrix implementing the permutation `π` of tensor factors. -/
noncomputable def permMatrix (π : Equiv.Perm E) :
    (Matrix (E → Fin (reducedDegree K B)) (E → Fin (reducedDegree K B)) (SF K B))ˣ :=
  permUnit (indexPerm π).symm

theorem splitRep_perm_eq_conj (π : Equiv.Perm E) (c : ⨂[K] _ : E, B) :
    splitRep K B E (permAlgEquiv K E B π c) =
      (permMatrix K B E π).val * splitRep K B E c * ((permMatrix K B E π)⁻¹).val := by
  rw [splitRep_perm, permMatrix, permUnit_conj]

theorem permMatrix_mul (π ρ : Equiv.Perm E) :
    permMatrix K B E (π * ρ) = permMatrix K B E π * permMatrix K B E ρ := by
  rw [permMatrix, permMatrix, permMatrix, ← permUnit_trans]
  congr 1

theorem permMatrix_one : permMatrix K B E 1 = 1 := by
  ext i j
  change ((indexPerm (1 : Equiv.Perm E)).symm.toPEquiv.toMatrix : Matrix _ _ (SF K B)) i j =
    (1 : Matrix _ _ (SF K B)) i j
  have : (indexPerm (1 : Equiv.Perm E) (m := reducedDegree K B)).symm = Equiv.refl _ := by
    ext i σ
    rfl
  rw [this, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

end Model

section Galois

variable (K : Type u) [Field K] (B : Type u) [Ring B] [Algebra K B] [FiniteDimensional K B]
  [Algebra.IsCentral K B] [IsSimpleRing B]
variable (E : Type w) [Fintype E] [DecidableEq E]

/-- The Galois action `h ⊗ 1` on the scalar extension of `⨂_K B`. -/
noncomputable def galTensor (h : SF K B ≃ₐ[K] SF K B) :
    SF K B ⊗[K] (⨂[K] _ : E, B) →ₐ[K] SF K B ⊗[K] (⨂[K] _ : E, B) :=
  Algebra.TensorProduct.map (h : SF K B →ₐ[K] SF K B) (AlgHom.id K _)

omit [Fintype E] [DecidableEq E] in
@[simp]
theorem galTensor_tmul (h : SF K B ≃ₐ[K] SF K B) (x : SF K B) (c : ⨂[K] _ : E, B) :
    galTensor K B E h (x ⊗ₜ c) = h x ⊗ₜ c := rfl

/-- The `SF`-algebra automorphism `χ ∘ (h ⊗ 1) ∘ χ⁻¹ ∘ (h⁻¹ on entries)` of `M_d(SF)`. -/
noncomputable def chartTwist (h : SF K B ≃ₐ[K] SF K B) :
    Matrix (Fin (reducedDegree K B)) (Fin (reducedDegree K B)) (SF K B) ≃ₐ[SF K B]
      Matrix (Fin (reducedDegree K B)) (Fin (reducedDegree K B)) (SF K B) :=
  AlgEquiv.ofRingEquiv
    (f := ((RingEquiv.mapMatrix h.symm.toRingEquiv).trans
      (finiteGaloisSplittingChart K B).symm.toRingEquiv).trans
      ((Algebra.TensorProduct.congr h (AlgEquiv.refl : B ≃ₐ[K] B)).toRingEquiv.trans
        (finiteGaloisSplittingChart K B).toRingEquiv))
    (fun x => by
      simp only [RingEquiv.trans_apply, RingEquiv.mapMatrix_apply, AlgEquiv.coe_ringEquiv]
      rw [Algebra.algebraMap_eq_smul_one, Matrix.map_smul', Matrix.map_one _ (map_zero _)
        (map_one _), ← Algebra.algebraMap_eq_smul_one]
      · rw [AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
        simp only [Algebra.algebraMap_self, RingHom.id_apply, AlgEquiv.coe_toAlgHom,
          AlgEquiv.apply_symm_apply, AlgEquiv.coe_refl, id_eq]
        rw [← Algebra.algebraMap_eq_smul_one]
        exact (finiteGaloisSplittingChart K B).commutes x
      · exact fun a b => map_mul h.symm a b)

/-- A unit `a_h` with `χ ((h ⊗ 1) y) = a_h · h(χ y) · a_h⁻¹`. -/
noncomputable def chartUnit (h : SF K B ≃ₐ[K] SF K B) :
    (Matrix (Fin (reducedDegree K B)) (Fin (reducedDegree K B)) (SF K B))ˣ :=
  (Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv (chartTwist K B h)).choose

theorem chart_galois (h : SF K B ≃ₐ[K] SF K B) (y : SF K B ⊗[K] B) :
    finiteGaloisSplittingChart K B (Algebra.TensorProduct.map (h : SF K B →ₐ[K] SF K B)
        (AlgHom.id K B) y) =
      (chartUnit K B h).val * (finiteGaloisSplittingChart K B y).map h *
        ((chartUnit K B h)⁻¹).val := by
  have hspec := (Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv
    (chartTwist K B h)).choose_spec ((finiteGaloisSplittingChart K B y).map h)
  rw [← chartUnit] at hspec
  rw [← hspec]
  simp only [chartTwist, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
    RingEquiv.mapMatrix_apply, AlgEquiv.coe_ringEquiv, Matrix.map_map]
  have hid : (⇑h.symm ∘ ⇑h) = id := funext h.symm_apply_apply
  rw [hid, Matrix.map_id, AlgEquiv.symm_apply_apply]
  rfl

end Galois

section Kron

variable (K : Type u) [Field K] (B : Type u) [Ring B] [Algebra K B] [FiniteDimensional K B]
  [Algebra.IsCentral K B] [IsSimpleRing B]
variable (E : Type w) [Fintype E] [DecidableEq E]

/-- The Kronecker power of the Skolem–Noether unit `a_h`. -/
noncomputable def kronUnit (h : SF K B ≃ₐ[K] SF K B) : (MatE K B E)ˣ where
  val := kroneckerMultilinear (SF K B) E (reducedDegree K B) (fun _ => (chartUnit K B h).val)
  inv := kroneckerMultilinear (SF K B) E (reducedDegree K B)
    (fun _ => ((chartUnit K B h)⁻¹).val)
  val_inv := by
    rw [← kroneckerMultilinear_mul]
    have : ((fun _ : E => (chartUnit K B h).val) * fun _ => ((chartUnit K B h)⁻¹).val) = 1 :=
      funext fun _ => Units.mul_inv _
    rw [this]
    exact kroneckerMultilinear_one _ _ _
  inv_val := by
    rw [← kroneckerMultilinear_mul]
    have : ((fun _ : E => ((chartUnit K B h)⁻¹).val) * fun _ => (chartUnit K B h).val) = 1 :=
      funext fun _ => Units.inv_mul _
    rw [this]
    exact kroneckerMultilinear_one _ _ _

omit [DecidableEq E] in
theorem kronecker_map_galois (h : SF K B ≃ₐ[K] SF K B) (A : E → MatB K B) :
    (kroneckerMultilinear (SF K B) E (reducedDegree K B) A).map h =
      kroneckerMultilinear (SF K B) E (reducedDegree K B) (fun σ => (A σ).map h) := by
  ext i j
  simp [map_prod]

theorem splitRep_galois (h : SF K B ≃ₐ[K] SF K B) (c : ⨂[K] _ : E, B) :
    splitRep K B E c =
      (kronUnit K B E h).val * (splitRep K B E c).map h * ((kronUnit K B E h)⁻¹).val := by
  induction c using PiTensorProduct.induction_on with
  | smul_tprod r b =>
    have hmap : ∀ X : MatE K B E, (r • X).map h = r • X.map h := by
      intro X
      ext i j
      simp [map_smul]
    rw [map_smul, hmap, Matrix.mul_smul, Matrix.smul_mul, splitRep_tprod, kronecker_map_galois]
    congr 1
    change _ = kroneckerMultilinear (SF K B) E (reducedDegree K B) (fun _ => (chartUnit K B h).val) *
      kroneckerMultilinear (SF K B) E (reducedDegree K B) (fun σ => (chartLin K B (b σ)).map h) *
      kroneckerMultilinear (SF K B) E (reducedDegree K B) (fun _ => ((chartUnit K B h)⁻¹).val)
    rw [← kroneckerMultilinear_mul, ← kroneckerMultilinear_mul]
    congr 1
    funext σ
    change chartLin K B (b σ) = (chartUnit K B h).val * (chartLin K B (b σ)).map h *
      ((chartUnit K B h)⁻¹).val
    rw [chartLin_apply, ← chart_galois, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  | add x y hx hy =>
    rw [map_add, Matrix.map_add _ (map_add h), mul_add, add_mul, ← hx, ← hy]

theorem splitTheta_galois (h : SF K B ≃ₐ[K] SF K B) (z : SF K B ⊗[K] (⨂[K] _ : E, B)) :
    splitTheta K B E (galTensor K B E h z) =
      (kronUnit K B E h).val * (splitTheta K B E z).map h * ((kronUnit K B E h)⁻¹).val := by
  induction z using TensorProduct.inductionOn with
  | tmul x c =>
    have hmap : ∀ X : MatE K B E, (x • X).map h = h x • X.map h := by
      intro X
      ext i j
      simp [map_mul]
    rw [galTensor_tmul, splitTheta_tmul, splitTheta_tmul, hmap, Matrix.mul_smul,
      Matrix.smul_mul, ← splitRep_galois]
  | add z w hz hw =>
    rw [map_add, map_add, hz, hw, map_add, Matrix.map_add _ (map_add h), mul_add, add_mul]

theorem permMatrix_galois (h : SF K B ≃ₐ[K] SF K B) (π : Equiv.Perm E) :
    (kronUnit K B E h).val * (permMatrix K B E π).val.map h * ((kronUnit K B E h)⁻¹).val =
      (permMatrix K B E π).val := by
  have hP : (permMatrix K B E π).val.map h = (permMatrix K B E π).val := by
    ext i j
    change h ((indexPerm π).symm.toPEquiv.toMatrix i j) = (indexPerm π).symm.toPEquiv.toMatrix i j
    rw [PEquiv.toMatrix_apply]
    split_ifs <;> simp
  have hK : (permMatrix K B E π).val * (kronUnit K B E h).val *
      ((permMatrix K B E π)⁻¹).val = (kronUnit K B E h).val := by
    rw [permMatrix, permUnit_conj]
    change (kroneckerMultilinear (SF K B) E (reducedDegree K B)
      (fun _ => (chartUnit K B h).val)).submatrix _ _ = _
    rw [← kroneckerMultilinear_reindex]
    rfl
  rw [hP]
  calc (kronUnit K B E h).val * (permMatrix K B E π).val * ((kronUnit K B E h)⁻¹).val
      = ((permMatrix K B E π).val * (kronUnit K B E h).val * ((permMatrix K B E π)⁻¹).val) *
          (permMatrix K B E π).val * ((kronUnit K B E h)⁻¹).val := by rw [hK]
    _ = (permMatrix K B E π).val := by
      simp only [mul_assoc, Units.inv_mul, mul_one, Units.mul_inv]

end Kron

section Descent

variable (K : Type u) [Field K] (B : Type u) [Ring B] [Algebra K B] [FiniteDimensional K B]
  [Algebra.IsCentral K B] [IsSimpleRing B]
variable (E : Type w) [Fintype E] [DecidableEq E]

/-- The Galois action `h ↦ h ⊗ 1` on `SF ⊗_K (⨂_K B)`. -/
noncomputable def galTensorAction :
    GaloisDescent.SemilinearAlgAction K (SF K B) (SF K B ⊗[K] (⨂[K] _ : E, B)) where
  act h := (galTensor K B E h).toRingHom.toAddMonoidHom
  one_act z := by
    induction z using TensorProduct.inductionOn with
    | tmul x c => rfl
    | add z w hz hw => simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
        map_add] at hz hw ⊢; rw [hz, hw]
  mul_act g h z := by
    induction z using TensorProduct.inductionOn with
    | tmul x c => rfl
    | add z w hz hw => simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
        map_add] at hz hw ⊢; rw [hz, hw]
  act_smul h x z := by
    induction z using TensorProduct.inductionOn with
    | tmul y c =>
      change galTensor K B E h (x • (y ⊗ₜ c)) = h x • galTensor K B E h (y ⊗ₜ c)
      rw [smul_tmul', galTensor_tmul, galTensor_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
        map_mul]
    | add z w hz hw =>
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, smul_add,
        map_add] at hz hw ⊢
      rw [hz, hw]
  act_one h := map_one (galTensor K B E h)
  act_mul h := map_mul (galTensor K B E h)

omit [Fintype E] [DecidableEq E] in
theorem tmul_one_injective :
    Function.Injective (fun c : ⨂[K] _ : E, B => (1 : SF K B) ⊗ₜ[K] c) :=
  Algebra.TensorProduct.includeRight_injective (A := SF K B) (algebraMap K (SF K B)).injective

omit [DecidableEq E] in
/-- Galois-fixed elements of the scalar extension come from `⨂_K B`. -/
theorem exists_tmul_eq_of_fixed (z : SF K B ⊗[K] (⨂[K] _ : E, B))
    (hz : ∀ h : SF K B ≃ₐ[K] SF K B, galTensor K B E h z = z) :
    ∃ c : ⨂[K] _ : E, B, (1 : SF K B) ⊗ₜ[K] c = z := by
  let ρ := galTensorAction K B E
  have : FiniteDimensional K (⨂[K] _ : E, B) := PiTensorProduct.finite
  have : FiniteDimensional K (SF K B ⊗[K] (⨂[K] _ : E, B)) :=
    Module.Finite.trans (SF K B) _
  let S := LinearMap.range
    ((Algebra.TensorProduct.includeRight : (⨂[K] _ : E, B) →ₐ[K] SF K B ⊗[K] _).toLinearMap)
  have hle : S ≤ Subalgebra.toSubmodule ρ.fixedSubalgebra := by
    rintro _ ⟨c, rfl⟩ h
    change galTensor K B E h (1 ⊗ₜ c) = 1 ⊗ₜ c
    rw [galTensor_tmul, map_one]
  have hfin : finrank K S = finrank K (Subalgebra.toSubmodule ρ.fixedSubalgebra) := by
    rw [LinearMap.finrank_range_of_inj (tmul_one_injective K B E)]
    change _ = finrank K ρ.fixedSubalgebra
    rw [ρ.finrank_fixedSubalgebra, Module.finrank_baseChange]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  have hmem : z ∈ S := by
    rw [heq]
    exact hz
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc⟩

theorem permMatrix_preimage_fixed (π : Equiv.Perm E) (h : SF K B ≃ₐ[K] SF K B) :
    galTensor K B E h ((splitThetaEquiv K B E).symm (permMatrix K B E π).val) =
      (splitThetaEquiv K B E).symm (permMatrix K B E π).val := by
  apply (splitThetaEquiv K B E).injective
  rw [AlgEquiv.apply_symm_apply, splitThetaEquiv_apply, splitTheta_galois,
    ← splitThetaEquiv_apply, AlgEquiv.apply_symm_apply]
  exact permMatrix_galois K B E h π

/-- The element of `⨂_K B` descending the permutation matrix of `π`. -/
noncomputable def permUnitVal (π : Equiv.Perm E) : ⨂[K] _ : E, B :=
  (exists_tmul_eq_of_fixed K B E _ (permMatrix_preimage_fixed K B E π)).choose

theorem tmul_permUnitVal (π : Equiv.Perm E) :
    (1 : SF K B) ⊗ₜ[K] permUnitVal K B E π =
      (splitThetaEquiv K B E).symm (permMatrix K B E π).val :=
  (exists_tmul_eq_of_fixed K B E _ (permMatrix_preimage_fixed K B E π)).choose_spec

omit [Fintype E] [DecidableEq E] in
theorem one_tmul_mul (a b : ⨂[K] _ : E, B) :
    (1 : SF K B) ⊗ₜ[K] (a * b) = ((1 : SF K B) ⊗ₜ[K] a) * ((1 : SF K B) ⊗ₜ[K] b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The permutation elements form a monoid homomorphism `Perm E →* ⨂_K B`. -/
noncomputable def permUnitHom : Equiv.Perm E →* (⨂[K] _ : E, B) where
  toFun := permUnitVal K B E
  map_one' := by
    apply tmul_one_injective K B E
    change (1 : SF K B) ⊗ₜ[K] permUnitVal K B E 1 = (1 : SF K B) ⊗ₜ[K] 1
    rw [tmul_permUnitVal, permMatrix_one, Units.val_one, map_one]
    rfl
  map_mul' π ρ := by
    apply tmul_one_injective K B E
    change (1 : SF K B) ⊗ₜ[K] permUnitVal K B E (π * ρ) =
      (1 : SF K B) ⊗ₜ[K] (permUnitVal K B E π * permUnitVal K B E ρ)
    rw [one_tmul_mul, tmul_permUnitVal, tmul_permUnitVal, tmul_permUnitVal, permMatrix_mul,
      Units.val_mul, map_mul]

/-- Units of `⨂_K B` implementing the permutations of the tensor factors. -/
noncomputable def permUnits : Equiv.Perm E →* (⨂[K] _ : E, B)ˣ :=
  (permUnitHom K B E).toHomUnits

theorem permUnits_val (π : Equiv.Perm E) :
    (permUnits K B E π).val = permUnitVal K B E π := rfl

/-- The permutation units implement the permutations of tensor factors by conjugation. -/
theorem permUnits_conj (π : Equiv.Perm E) (c : ⨂[K] _ : E, B) :
    (permUnits K B E π).val * c * ((permUnits K B E π)⁻¹).val = permAlgEquiv K E B π c := by
  rw [← map_inv, permUnits_val, permUnits_val]
  apply tmul_one_injective K B E
  change (1 : SF K B) ⊗ₜ[K] (permUnitVal K B E π * c * permUnitVal K B E π⁻¹) =
    (1 : SF K B) ⊗ₜ[K] permAlgEquiv K E B π c
  rw [one_tmul_mul, one_tmul_mul, tmul_permUnitVal, tmul_permUnitVal]
  apply (splitThetaEquiv K B E).injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have hθ : ∀ d : ⨂[K] _ : E, B, splitThetaEquiv K B E ((1 : SF K B) ⊗ₜ[K] d) =
      splitRep K B E d := fun d => by
    rw [splitThetaEquiv_apply, splitTheta_tmul, one_smul]
  rw [hθ, hθ, splitRep_perm_eq_conj]
  have hinv : (permMatrix K B E π⁻¹).val = ((permMatrix K B E π)⁻¹).val := by
    have h1 : permMatrix K B E π⁻¹ * permMatrix K B E π = 1 := by
      rw [← permMatrix_mul, inv_mul_cancel, permMatrix_one]
    rw [eq_inv_of_mul_eq_one_left h1]
  rw [hinv]

end Descent

end Langlands.BrauerCorestriction
