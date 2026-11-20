import Langlands.Representation.Archimedean.LowerVermaShiftedCharacter
import Langlands.Representation.Archimedean.ComplexGenericLargeReduction
import Langlands.Automorphic.ComplexPlaceParameterWeights
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Upper triangular highest-weight characters

See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.VermaShifted

attribute [local instance 100] LieRing.ofAssociativeRing

open VermaGL InfinitesimalCharacter Langlands.Automorphic.ComplexPlaceParameter

variable (n : ℕ)

private def reversalMatrix : Matrix (Fin n) (Fin n) ℂ := (Fin.revPerm (n := n)).permMatrix ℂ

private theorem reversalMatrix_sq : reversalMatrix n * reversalMatrix n = 1 := by
  have h : (Fin.revPerm : Equiv.Perm (Fin n)) * Fin.revPerm = 1 := by
    apply Equiv.ext
    intro i
    exact Fin.rev_rev i
  rw [reversalMatrix, ← Matrix.permMatrix_mul, h, Matrix.permMatrix_one]

private def reversalUnit : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := reversalMatrix n
  inv := reversalMatrix n
  val_inv := reversalMatrix_sq n
  inv_val := reversalMatrix_sq n

private def reverseU : glU n →ₐ[ℂ] glU n := envMap (ComplexGenericLarge.conjLieB (reversalUnit n))

private theorem reverseU_unitU (p q : Fin n) :
    reverseU n (unitU n p q) = unitU n p.rev q.rev := by
  rw [reverseU, envMap_ι, ComplexGenericLarge.conjLieB_apply]
  change UniversalEnvelopingAlgebra.ι ℂ
      (reversalMatrix n * Matrix.single p q 1 * reversalMatrix n) = _
  congr 1
  unfold reversalMatrix Equiv.Perm.permMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Fin.revPerm_symm]
  ext i j
  simp [Matrix.single_apply, Fin.rev_eq_iff]

private theorem reverseU_center (z : VermaGL.center n) : reverseU n z = z := by
  let e : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (1 - reversalMatrix n)
  have he : e * e = e := by
    dsimp only [e]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub, mul_sub, reversalMatrix_sq]
    simp only [one_mul, mul_one]
    module
  have hw : (reversalUnit n : Matrix (Fin n) (Fin n) ℂ) = 1 + ((-1 : ℂ) - 1) • e := by
    change reversalMatrix n = _
    dsimp only [e]
    module
  exact ComplexGenericLarge.envMap_conjLieB_idempotent he (by norm_num) (reversalUnit n) hw z.2

/-- Center character on an upper triangular highest-weight vector of weight `mu`. -/
def upperCharacter (mu : Fin n → ℂ) : VermaGL.center n →ₐ[ℂ] ℂ :=
  character n (fun i => mu i.rev)

/-- A concrete upper Verma action on the lower Verma module with reversed weight. -/
def upperAction (mu : Fin n → ℂ) : glU n →ₐ[ℂ] Module.End ℂ (LowerVerma n (fun i => mu i.rev)) :=
  (Algebra.lsmul ℂ ℂ _).comp (reverseU n)

theorem upperAction_unitU_of_lt (mu : Fin n → ℂ) {p q : Fin n} (hpq : p < q) :
    upperAction n mu (unitU n p q) (gen n (fun i => mu i.rev)) = 0 := by
  rw [upperAction, AlgHom.comp_apply, reverseU_unitU, Algebra.lsmul_apply]
  exact BGChase.unitU_smul_gen_of_lt _ (Fin.rev_lt_rev.mpr hpq)

theorem upperAction_unitU_diag (mu : Fin n → ℂ) (p : Fin n) :
    upperAction n mu (unitU n p p) (gen n (fun i => mu i.rev)) =
      mu p • gen n (fun i => mu i.rev) := by
  rw [upperAction, AlgHom.comp_apply, reverseU_unitU, Algebra.lsmul_apply,
    BGChase.unitU_smul_gen_diag]
  simp only [Fin.rev_rev]

/-- The center action on an arbitrary upper highest-weight vector. -/
theorem upperCharacter_action (mu : Fin n → ℂ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : glU n →ₐ[ℂ] Module.End ℂ V) (v : V)
    (hu : ∀ p q : Fin n, p < q → A (unitU n p q) v = 0)
    (hd : ∀ p : Fin n, A (unitU n p p) v = mu p • v) (z : VermaGL.center n) :
    A z v = upperCharacter n mu z • v := by
  have h := character_action n (fun i => mu i.rev) (A.comp (reverseU n)) v
    (fun p q h => by rw [AlgHom.comp_apply, reverseU_unitU, hu _ _ (Fin.rev_lt_rev.mpr h)])
    (fun p => by rw [AlgHom.comp_apply, reverseU_unitU, hd]) z
  rwa [AlgHom.comp_apply, reverseU_center] at h

private theorem finRev_add (i : Fin n) : (i.rev.val : ℂ) + (i.val : ℂ) = (n : ℂ) - 1 := by
  have h : i.rev.val + i.val + 1 = n := by
    have hi := i.isLt
    change n - (i.val + 1) + i.val + 1 = n
    omega
  exact eq_sub_of_add_eq (by exact_mod_cast h)

private theorem character_eq_iff_ofFn (lam mu : Fin n → ℂ) :
    character n lam = character n mu ↔
      (List.ofFn fun i => lam i + (i.val : ℂ)).Perm (List.ofFn fun i => mu i + (i.val : ℂ)) := by
  rw [character_eq_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    have heq : (fun i => lam i + (i.val : ℂ)) = (fun i => mu i + (i.val : ℂ)) ∘ σ := funext hσ
    rw [heq]
    exact σ.ofFn_comp_perm _
  · intro h
    refine GelfandSeparation.exists_perm_of_map_eq
      (f := fun i => lam i + (i.val : ℂ)) (g := fun i => mu i + (i.val : ℂ)) ?_
    simpa only [Finset.val_univ_fin, Multiset.map_coe, ← List.ofFn_eq_map] using
      Multiset.coe_eq_coe.mpr h

private theorem add_common_shift_iff (x y : Fin n → ℂ) (c : ℂ) :
    (List.ofFn fun i => x i + c).Perm (List.ofFn fun i => y i + c) ↔
      (List.ofFn x).Perm (List.ofFn y) := by
  constructor
  · intro h
    simpa [List.map_ofFn, Function.comp_def] using h.map (· - c)
  · intro h
    simpa only [List.map_ofFn, Function.comp_def] using h.map (· + c)

private theorem reversed_shift_perm (mu : Fin n → ℂ) :
    (List.ofFn fun i => mu i.rev + (i.val : ℂ)).Perm
      (List.ofFn fun i => mu i + rho n i + ((n : ℂ) - 1) / 2) := by
  have h : (fun i : Fin n => mu i.rev + (i.val : ℂ)) =
      (fun i => mu i + rho n i + ((n : ℂ) - 1) / 2) ∘ Fin.revPerm := by
    funext i
    have hrev := finRev_add n i
    change mu i.rev + i.val = mu i.rev + rho n i.rev + ((n : ℂ) - 1) / 2
    unfold rho
    linear_combination hrev
  rw [h]
  exact Fin.revPerm.ofFn_comp_perm _

/-- Equality of upper highest-weight characters is equality of the `mu + rho` orbits. -/
theorem upperCharacter_eq_iff (mu nu : Fin n → ℂ) :
    upperCharacter n mu = upperCharacter n nu ↔
      (List.ofFn fun i => mu i + rho n i).Perm (List.ofFn fun i => nu i + rho n i) := by
  rw [upperCharacter, upperCharacter, character_eq_iff_ofFn]
  rw [← add_common_shift_iff n (fun i => mu i + rho n i) (fun i => nu i + rho n i)
    (((n : ℂ) - 1) / 2)]
  exact ⟨fun h => (reversed_shift_perm n mu).symm.trans (h.trans (reversed_shift_perm n nu)),
    fun h => (reversed_shift_perm n mu).trans (h.trans (reversed_shift_perm n nu).symm)⟩

/-- A normalized diagonal exponent list gives the corresponding upper highest-weight character. -/
theorem character_add_rho_eq_upper (x mu : Fin n → ℂ)
    (h : (List.ofFn x).Perm (List.ofFn fun i => mu i + rho n i)) :
    character n (fun i => x i + rho n i) = upperCharacter n mu := by
  rw [upperCharacter, character_eq_iff_ofFn]
  have hshift : (fun i => x i + rho n i + (i.val : ℂ)) =
      (fun i => x i + ((n : ℂ) - 1) / 2) := by
    funext i
    unfold rho
    ring
  rw [hshift]
  exact ((add_common_shift_iff n _ _ (((n : ℂ) - 1) / 2)).mpr h).trans
    (reversed_shift_perm n mu).symm

end Langlands.Archimedean.VermaShifted
