import Langlands.Algebra.KroneckerInduction
import Langlands.GroupScheme.MatrixRepresentation.Reindex
import Langlands.GroupScheme.Reductive.TensorWeights
import Langlands.GroupScheme.Reductive.HighestWeightSubquotientRepresentation

/-! # Tensor products of finite families of representations and their top weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix Kronecker CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.Algebra.KroneckerInduction

section PiTensor

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- A Kronecker product over `Fin 1` is its only factor, reindexed. -/
theorem piKronecker_fin_one {A : Type*} [CommRing A] (Z : Fin 1 → Matrix n n A) :
    piKronecker Z = (Z 0).submatrix (Equiv.funUnique (Fin 1) n) (Equiv.funUnique (Fin 1) n) := by
  ext a b
  rw [piKronecker_apply, Fin.prod_univ_one]
  rfl

omit [Fintype n] [DecidableEq n] in
/-- A Kronecker product over `Fin (m + 1)` is the Kronecker product of its first factor with
the Kronecker product of the others, reindexed along `Fin.consEquiv`. -/
theorem piKronecker_fin_succ {A : Type*} [CommRing A] {m : ℕ} (Z : Fin (m + 1) → Matrix n n A) :
    piKronecker Z = ((Z 0) ⊗ₖ piKronecker (fun i => Z i.succ)).submatrix
      (Fin.consEquiv fun _ => n).symm (Fin.consEquiv fun _ => n).symm := by
  ext a b
  rw [piKronecker_apply, Fin.prod_univ_succ]
  rfl

/-- The tensor product of a family of representations indexed by `Fin (m + 1)`, on the
coordinates `Fin (m + 1) → n`. It is built from the published binary tensor product and
reindexing: `ρ 0 ⊗ (ρ 1 ⊗ (⋯))`, reindexed along `Fin.consEquiv` at each step. -/
def piTensor : {m : ℕ} → (Fin (m + 1) → MatrixRepresentation G n) →
    MatrixRepresentation G (Fin (m + 1) → n)
  | 0, ρ => (ρ 0).reindex (Equiv.funUnique (Fin 1) n).symm
  | _ + 1, ρ => ((ρ 0).tensor (piTensor fun i => ρ i.succ)).reindex (Fin.consEquiv fun _ => n)

/-- On every affine test point, the matrix of `piTensor ρ` is the Kronecker product of the
matrices of the `ρ i`. -/
theorem piTensor_affineMatrix : {m : ℕ} → (ρ : Fin (m + 1) → MatrixRepresentation G n) →
    (A : CommAlgCat.{u} R) → (x : (algSpec R).obj (op A) ⟶ G.X) →
    ((piTensor ρ).affineMatrix A x : Matrix (Fin (m + 1) → n) (Fin (m + 1) → n) A) =
      piKronecker fun i => ((ρ i).affineMatrix A x : Matrix n n A)
  | 0, ρ, A, x => by
    rw [piTensor, reindex_affineMatrix, reindexGL_val, piKronecker_fin_one, Equiv.symm_symm]
  | m + 1, ρ, A, x => by
    rw [piTensor, reindex_affineMatrix, reindexGL_val, tensor_affineMatrix,
      GeneralLinear.kroneckerHom_coe, piTensor_affineMatrix (fun i => ρ i.succ) A x,
      piKronecker_fin_succ (fun i => ((ρ i).affineMatrix A x : Matrix n n A))]

end PiTensor

section Reindex

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The coordinate permutation matrix of a reindexing. -/
def reindexMatrix (e : n ≃ m) : Matrix m n k :=
  (1 : Matrix n n k).submatrix e.symm id

omit [Fintype m] in
theorem reindexMatrix_mul_reindexMatrix_symm (e : n ≃ m) :
    reindexMatrix (k := k) e * reindexMatrix (k := k) e.symm = 1 := by
  ext i j
  simp only [reindexMatrix, Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply,
    Equiv.symm_symm]
  rw [Finset.sum_eq_single (e.symm i)]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

/-- Reindexing is intertwined by the coordinate permutation matrix. -/
theorem intertwines_reindex (ρ : MatrixRepresentation G n) (e : n ≃ m) :
    Intertwines ρ (ρ.reindex e) (reindexMatrix e) := by
  intro S x
  rw [reindex_affineMatrix, reindexGL_val]
  set M := (ρ.affineMatrix S x : Matrix n n S)
  have hC : (reindexMatrix (k := k) e).map (algebraMap k S) =
      (1 : Matrix n n S).submatrix e.symm id := by
    ext i j
    simp only [reindexMatrix, Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    split_ifs <;> simp
  rw [hC]
  ext i j
  have lhs : ((1 : Matrix n n S).submatrix e.symm id * M) i j = M (e.symm i) j := by
    simp [Matrix.mul_apply, Matrix.one_apply]
  have rhs : (M.submatrix e.symm e.symm * (1 : Matrix n n S).submatrix e.symm id) i j =
      M (e.symm i) j := by
    rw [Matrix.submatrix_mul_equiv M (1 : Matrix n n S) e.symm e.symm id, Matrix.mul_one]
    rfl
  rw [lhs, rhs]

end Reindex

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation

variable {F : Type u} [Field F]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
  (p : SplitPinning H) {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `lam` is a top weight of `ρ`: it has multiplicity one, and every weight of `ρ` lies
below it. This is the part of `IsHighestWeight` that does not involve irreducibility. -/
def HasTopWeight (ρ : MatrixRepresentation H n) (lam : characterLattice p.torus) : Prop :=
  Module.finrank F (p.representationWeightSpace ρ lam) = 1 ∧
    ∀ mu, p.representationWeightSpace ρ mu ≠ ⊥ → lam - mu ∈ p.positiveRootMonoid

variable {p}

theorem IsHighestWeight.hasTopWeight {ρ : MatrixRepresentation H n}
    {lam : characterLattice p.torus} (h : p.IsHighestWeight ρ lam) : p.HasTopWeight ρ lam :=
  ⟨h.2.2.1, h.2.2.2⟩

variable {ρ : MatrixRepresentation H n} {τ : MatrixRepresentation H m}
  {lam mu : characterLattice p.torus}

theorem HasTopWeight.tensorWeightSpan_eq_bot_of_ne (hρ : p.HasTopWeight ρ lam)
    (hτ : p.HasTopWeight τ mu) {α β : characterLattice p.torus} (h : α + β = lam + mu)
    (hne : (α, β) ≠ (lam, mu)) : p.tensorWeightSpan ρ τ α β = ⊥ := by
  by_cases hα : p.representationWeightSpace ρ α = ⊥
  · exact p.tensorWeightSpan_eq_bot_left ρ τ hα
  by_cases hβ : p.representationWeightSpace τ β = ⊥
  · exact p.tensorWeightSpan_eq_bot_right ρ τ hβ
  obtain ⟨h1, h2⟩ := p.eq_of_add_eq_of_sub_mem (hρ.2 α hα) (hτ.2 β hβ) h
  exact absurd (Prod.ext h1 h2) hne

theorem HasTopWeight.representationWeightSpace_tensor_add (hρ : p.HasTopWeight ρ lam)
    (hτ : p.HasTopWeight τ mu) :
    p.representationWeightSpace (ρ.tensor τ) (lam + mu) = p.tensorWeightSpan ρ τ lam mu := by
  rw [representationWeightSpace_tensor]
  apply le_antisymm
  · refine iSup₂_le fun ab hab => ?_
    by_cases hab' : ab = (lam, mu)
    · subst hab'
      exact le_rfl
    · rw [hρ.tensorWeightSpan_eq_bot_of_ne hτ hab (by simpa using hab')]
      exact bot_le
  · exact le_iSup₂ (f := fun (ab : characterLattice p.torus × characterLattice p.torus)
      (_ : ab.1 + ab.2 = lam + mu) => p.tensorWeightSpan ρ τ ab.1 ab.2) (lam, mu) rfl

theorem HasTopWeight.finrank_tensor (hρ : p.HasTopWeight ρ lam) (hτ : p.HasTopWeight τ mu) :
    Module.finrank F (p.representationWeightSpace (ρ.tensor τ) (lam + mu)) = 1 := by
  obtain ⟨v₀, hv₀, hv⟩ := finrank_eq_one_iff'.mp hρ.1
  obtain ⟨w₀, hw₀, hw⟩ := finrank_eq_one_iff'.mp hτ.1
  set x : n × m → F := fun ij => (v₀ : n → F) ij.1 * (w₀ : m → F) ij.2 with hx
  have hx0 : x ≠ 0 := by
    have hv₀' : (v₀ : n → F) ≠ 0 := fun h => hv₀ (Subtype.ext h)
    have hw₀' : (w₀ : m → F) ≠ 0 := fun h => hw₀ (Subtype.ext h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv₀'
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hw₀'
    intro h
    have := congrFun h (i, j)
    simp only [hx, Pi.zero_apply, mul_eq_zero] at this hi hj
    tauto
  have heq : p.tensorWeightSpan ρ τ lam mu = F ∙ x := by
    apply le_antisymm
    · rw [tensorWeightSpan, Submodule.span_le]
      rintro _ ⟨v, hvm, w, hwm, rfl⟩
      obtain ⟨c, hc⟩ := hv ⟨v, hvm⟩
      obtain ⟨d, hd⟩ := hw ⟨w, hwm⟩
      have hc' : v = c • (v₀ : n → F) := (congrArg Subtype.val hc).symm
      have hd' : w = d • (w₀ : m → F) := (congrArg Subtype.val hd).symm
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨c * d, ?_⟩
      funext ij
      simp only [hx, hc', hd', Pi.smul_apply, smul_eq_mul]
      ring
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨v₀, v₀.2, w₀, w₀.2, rfl⟩
  rw [hρ.representationWeightSpace_tensor_add hτ, heq, finrank_span_singleton hx0]

theorem HasTopWeight.sub_mem_tensor (hρ : p.HasTopWeight ρ lam) (hτ : p.HasTopWeight τ mu)
    (nu : characterLattice p.torus) (hnu : p.representationWeightSpace (ρ.tensor τ) nu ≠ ⊥) :
    lam + mu - nu ∈ p.positiveRootMonoid := by
  by_contra hcon
  apply hnu
  rw [representationWeightSpace_tensor, eq_bot_iff]
  refine iSup₂_le fun ab hab => ?_
  by_cases hα : p.representationWeightSpace ρ ab.1 = ⊥
  · rw [p.tensorWeightSpan_eq_bot_left ρ τ hα]
  by_cases hβ : p.representationWeightSpace τ ab.2 = ⊥
  · rw [p.tensorWeightSpan_eq_bot_right ρ τ hβ]
  exfalso
  apply hcon
  have := add_mem (hρ.2 ab.1 hα) (hτ.2 ab.2 hβ)
  rwa [show lam - ab.1 + (mu - ab.2) = lam + mu - (ab.1 + ab.2) by abel, hab] at this

/-- **Top weights of tensor products.** -/
theorem HasTopWeight.tensor (hρ : p.HasTopWeight ρ lam) (hτ : p.HasTopWeight τ mu) :
    p.HasTopWeight (ρ.tensor τ) (lam + mu) :=
  ⟨hρ.finrank_tensor hτ, hρ.sub_mem_tensor hτ⟩

/-- A top weight is maximal among the weights. -/
theorem HasTopWeight.eq_of_sub_mem (h : p.HasTopWeight ρ lam) {mu : characterLattice p.torus}
    (hmu : p.representationWeightSpace ρ mu ≠ ⊥) (hsub : mu - lam ∈ p.positiveRootMonoid) :
    mu = lam :=
  sub_eq_zero.mp (p.eq_zero_of_mem_positiveRootMonoid_of_neg_mem hsub
    (by rw [neg_sub]; exact h.2 mu hmu))

/-- Top weights are transported along invertible intertwiners. -/
theorem HasTopWeight.of_intertwines {C : Matrix m n F} {C' : Matrix n m F}
    (hC : Intertwines ρ τ C) (h1 : C' * C = 1) (h2 : C * C' = 1) (h : p.HasTopWeight ρ lam) :
    p.HasTopWeight τ lam := by
  have hsurj : Function.Surjective C.mulVecLin := fun v =>
    ⟨C' *ᵥ v, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]⟩
  have hinj : Function.Injective C.mulVecLin := fun v w hvw => by
    have := congrArg (C' *ᵥ ·) hvw
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
  have hmap := fun mu => Intertwines.map_weightSpace_eq_of_surjective p hC hsurj mu
  refine ⟨?_, fun mu hmu => h.2 mu ?_⟩
  · rw [hmap, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _).symm, h.1]
  · rw [hmap] at hmu
    intro hb
    rw [hb, Submodule.map_bot] at hmu
    exact hmu rfl

/-- Top weights are preserved by reindexing. -/
theorem HasTopWeight.reindex (h : p.HasTopWeight ρ lam) (e : n ≃ m) :
    p.HasTopWeight (ρ.reindex e) lam :=
  h.of_intertwines (intertwines_reindex ρ e)
    (by simpa using reindexMatrix_mul_reindexMatrix_symm (k := F) e.symm)
    (reindexMatrix_mul_reindexMatrix_symm e)

/-- **Top weights of tensor products of families.** If each `ρ i` has top weight `lam i`, then
`piTensor ρ` has top weight `∑ i, lam i`. -/
theorem HasTopWeight.piTensor : {m : ℕ} → {ρ : Fin (m + 1) → MatrixRepresentation H n} →
    {lam : Fin (m + 1) → characterLattice p.torus} → (∀ i, p.HasTopWeight (ρ i) (lam i)) →
    p.HasTopWeight (MatrixRepresentation.piTensor ρ) (∑ i, lam i)
  | 0, ρ, lam, h => by
    rw [Fin.sum_univ_one]
    exact (h 0).reindex _
  | m + 1, ρ, lam, h => by
    rw [Fin.sum_univ_succ]
    exact ((h 0).tensor (HasTopWeight.piTensor fun i => h i.succ)).reindex _

end Langlands.GroupScheme.SplitPinning
