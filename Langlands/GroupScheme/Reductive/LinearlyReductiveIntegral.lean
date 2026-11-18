import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Chevalley.SubspaceMatrix
import Langlands.GroupScheme.Unipotent.HopfFixed

/-! # Linear reductivity and local right integrals on the coordinate bialgebra -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.LinearReductivity

open AffineLinearEmbedding MatrixRepresentation

/-! ### Stable subspaces form a complete sublattice -/

section Lattice

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation H n)

/-- The linear map `v ↦ ℓ (g v)` attached to an affine point `g` and a functional `ℓ`. -/
def coefficientMap (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ H.X) (ℓ : A →ₗ[k] k) :
    (n → k) →ₗ[k] (n → k) where
  toFun v := fun i => ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
    (fun j => algebraMap k A (v j))) i)
  map_add' v w := by
    funext i
    have hv : (fun j => algebraMap k A ((v + w) j)) =
        (fun j => algebraMap k A (v j)) + fun j => algebraMap k A (w j) := by
      funext j
      simp
    change ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ fun j => algebraMap k A ((v + w) j)) i) =
      ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ fun j => algebraMap k A (v j)) i) +
        ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ fun j => algebraMap k A (w j)) i)
    rw [hv, Matrix.mulVec_add, Pi.add_apply, map_add]
  map_smul' c v := by
    funext i
    have hv : (fun j => algebraMap k A ((c • v) j)) = c • fun j => algebraMap k A (v j) := by
      funext j
      simp [Algebra.smul_def]
    change ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ fun j => algebraMap k A ((c • v) j)) i) =
      c • ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ fun j => algebraMap k A (v j)) i)
    rw [hv, Matrix.mulVec_smul, Pi.smul_apply, map_smul]

theorem isStableSubspace_iff_le (W : Submodule k (n → k)) :
    ρ.IsStableSubspace W ↔ ∀ A x ℓ, W ≤ W.comap (coefficientMap ρ A x ℓ) :=
  ⟨fun h A x ℓ _ hv => h A x _ hv ℓ, fun h A x _ hv ℓ => h A x ℓ hv⟩

theorem isStableSubspace_sSup (S : Set (Submodule k (n → k)))
    (hS : ∀ W ∈ S, ρ.IsStableSubspace W) : ρ.IsStableSubspace (sSup S) := by
  rw [isStableSubspace_iff_le]
  intro A x ℓ
  refine sSup_le fun W hW => ?_
  exact ((isStableSubspace_iff_le ρ W).mp (hS W hW) A x ℓ).trans
    (Submodule.comap_mono (le_sSup hW))

theorem isStableSubspace_sup {W W' : Submodule k (n → k)} (hW : ρ.IsStableSubspace W)
    (hW' : ρ.IsStableSubspace W') : ρ.IsStableSubspace (W ⊔ W') := by
  rw [← sSup_pair]
  refine isStableSubspace_sSup ρ _ fun U hU => ?_
  rcases hU with rfl | rfl
  · exact hW
  · exact hW'

theorem isStableSubspace_inf {W W' : Submodule k (n → k)} (hW : ρ.IsStableSubspace W)
    (hW' : ρ.IsStableSubspace W') : ρ.IsStableSubspace (W ⊓ W') :=
  fun A x v hv ℓ => ⟨hW A x v hv.1 ℓ, hW' A x v hv.2 ℓ⟩

theorem isStableSubspace_top : ρ.IsStableSubspace ⊤ :=
  fun _ _ _ _ _ => Submodule.mem_top

theorem isStableSubspace_bot : ρ.IsStableSubspace ⊥ := fun _ _ _ hv _ => by
  rw [(Submodule.mem_bot k).mp hv, Submodule.mem_bot]
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- The stable subspaces that are simple: nonzero, with no stable subspaces strictly between
`⊥` and themselves. -/
def simpleStable : Set (Submodule k (n → k)) :=
  {W | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W}

/-- Every nonzero stable subspace contains a simple stable subspace. -/
theorem exists_simpleStable_le {C : Submodule k (n → k)} (hC : ρ.IsStableSubspace C)
    (hC0 : C ≠ ⊥) : ∃ S ∈ simpleStable ρ, S ≤ C := by
  induction h : Module.finrank k C using Nat.strong_induction_on generalizing C with
  | _ m ih =>
    by_cases hs : ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ C → U = ⊥ ∨ U = C
    · exact ⟨C, ⟨hC, hC0, hs⟩, le_rfl⟩
    · push Not at hs
      obtain ⟨U, hU, hUC, hU0, hUC'⟩ := hs
      have hlt : Module.finrank k U < m := h ▸
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hUC hUC')
      obtain ⟨S, hS, hSU⟩ := ih _ hlt hU hU0 rfl
      exact ⟨S, hS, hSU.trans hUC⟩

/-- If every stable subspace has a stable complement, the simple stable subspaces span. -/
theorem sSup_simpleStable_eq_top
    (h : ∀ W, ρ.IsStableSubspace W → ∃ C, ρ.IsStableSubspace C ∧ IsCompl W C) :
    sSup (simpleStable ρ) = ⊤ := by
  obtain ⟨C, hC, hcompl⟩ := h _ (isStableSubspace_sSup ρ _ fun W (hW : W ∈ simpleStable ρ) => hW.1)
  by_cases hC0 : C = ⊥
  · subst hC0
    exact eq_top_of_isCompl_bot hcompl
  · exfalso
    obtain ⟨S, hS, hSC⟩ := exists_simpleStable_le ρ hC hC0
    have hle : S ≤ sSup (simpleStable ρ) ⊓ C := le_inf (le_sSup hS) hSC
    rw [hcompl.inf_eq_bot] at hle
    exact hS.2.1 (le_bot_iff.mp hle)

/-- If the simple stable subspaces span, every stable subspace has a stable complement. -/
theorem exists_isCompl_of_sSup_simpleStable (htop : sSup (simpleStable ρ) = ⊤)
    {W : Submodule k (n → k)} (hW : ρ.IsStableSubspace W) :
    ∃ C, ρ.IsStableSubspace C ∧ IsCompl W C := by
  let Ω : Set (Submodule k (n → k)) := {C | ρ.IsStableSubspace C ∧ Disjoint W C}
  have hne : Ω.Nonempty := ⟨⊥, isStableSubspace_bot ρ, disjoint_bot_right⟩
  obtain ⟨C, ⟨hC, hWC⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian k (n → k)) Ω hne
  refine ⟨C, hC, hWC, ?_⟩
  rw [codisjoint_iff, eq_top_iff, ← htop]
  refine sSup_le fun S hS => ?_
  by_contra hSle
  have hdisj : Disjoint (W ⊔ C) S := by
    rcases hS.2.2 _ (isStableSubspace_inf ρ (isStableSubspace_sup ρ hW hC) hS.1)
      inf_le_right with h0 | hSS
    · exact disjoint_iff.mpr h0
    · exact absurd (hSS ▸ inf_le_left) hSle
  refine hmax (C ⊔ S) ⟨isStableSubspace_sup ρ hC hS.1,
    Disjoint.disjoint_sup_right_of_disjoint_sup_left hWC hdisj⟩ (lt_of_le_of_ne le_sup_left ?_)
  intro hCS
  exact hSle (le_sup_of_le_right (hCS ▸ le_sup_right))

end Lattice

/-! ### The universal matrix of a presentation -/

section Universal

open Algebra.TensorProduct (includeLeft includeRight)

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (ψ : (algSpec (CommRingCat.of k)).obj (op B) ≅ H.X)
  {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation H n)

/-- The universal matrix of `ρ` for the presentation `ψ`: its matrix at the universal point. -/
abbrev univMatrix : GL n B := ρ.affineMatrix B ψ.hom

/-- The matrix at the point classified by an algebra map is the image of the universal matrix. -/
theorem affineMatrix_pt (A : CommAlgCat.{u} (CommRingCat.of k))
    (f : B →ₐ[CommRingCat.of k] A) :
    ρ.affineMatrix A (pt (corepresentableBy H ψ) f) =
      Matrix.GeneralLinearGroup.map f.toRingHom (univMatrix ψ ρ) :=
  ρ.affineMatrix_naturality (CommAlgCat.ofHom f) ψ.hom

/-- Every matrix of `ρ` is the image of the universal matrix. -/
theorem affineMatrix_eq_map (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ H.X) :
    ρ.affineMatrix A x = Matrix.GeneralLinearGroup.map
      ((corepresentableBy H ψ).homEquiv.symm x).hom.toRingHom (univMatrix ψ ρ) := by
  rw [← affineMatrix_pt ψ ρ A]
  exact congrArg (ρ.affineMatrix A) (pt_homEquiv_symm (corepresentableBy H ψ) x).symm

/-- Stability is stability under the universal matrix, tested by all linear functionals. -/
theorem isStableSubspace_iff_univ (W : Submodule k (n → k)) :
    ρ.IsStableSubspace W ↔ ∀ v ∈ W, ∀ ℓ : B →ₗ[k] k,
      (fun i => ℓ (((univMatrix ψ ρ : Matrix n n B) *ᵥ fun j => algebraMap k B (v j)) i)) ∈ W := by
  refine ⟨fun h v hv ℓ => h B ψ.hom v hv ℓ, fun h A x v hv ℓ => ?_⟩
  set f := ((corepresentableBy H ψ).homEquiv.symm x).hom
  have hc := h v hv (ℓ.comp (f.toLinearMap.restrictScalars k))
  convert hc using 1
  funext i
  rw [affineMatrix_eq_map ψ ρ A x]
  change ℓ (((univMatrix ψ ρ : Matrix n n B).map f.toRingHom *ᵥ
    fun j => algebraMap k A (v j)) i) = ℓ (f.toRingHom _)
  congr 1
  rw [RingHom.map_mulVec]
  congr 1
  funext j
  exact (f.commutes (v j)).symm

/-- Multiplicativity of the universal matrix: its image under the comultiplication is the
product of its images in the two tensor factors. -/
theorem univMatrix_comul :
    Matrix.GeneralLinearGroup.map (comul (corepresentableBy H ψ)).toRingHom (univMatrix ψ ρ) =
      Matrix.GeneralLinearGroup.map
          (includeLeft : B →ₐ[CommRingCat.of k] B ⊗[CommRingCat.of k] B).toRingHom
          (univMatrix ψ ρ) *
        Matrix.GeneralLinearGroup.map
          (includeRight : B →ₐ[CommRingCat.of k] B ⊗[CommRingCat.of k] B).toRingHom
          (univMatrix ψ ρ) := by
  rw [← affineMatrix_pt ψ ρ (CommAlgCat.of _ (B ⊗[CommRingCat.of k] B)),
    ← affineMatrix_pt ψ ρ (CommAlgCat.of _ (B ⊗[CommRingCat.of k] B)),
    ← affineMatrix_pt ψ ρ (CommAlgCat.of _ (B ⊗[CommRingCat.of k] B)), pt_comul]
  exact map_mul (ρ.affineMatrix (CommAlgCat.of _ (B ⊗[CommRingCat.of k] B))) _ _

end Universal

/-! ### Averaging with local right integrals -/

section Averaging

open Algebra.TensorProduct (includeLeft includeRight)

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (ψ : (algSpec (CommRingCat.of k)).obj (op B) ≅ H.X)
  {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation H n)

/-- The coordinate algebra of the presentation `ψ` has local normalized right integrals: for
every finite set `T` of coordinates there is a functional `r` with `r 1 = 1` such that
contracting the first comultiplication factor of each `y ∈ T` with `r` gives `r y • 1`. -/
def HasLocalRightIntegrals : Prop :=
  letI := (bialgebra (corepresentableBy H ψ)).toCoalgebra
  ∀ T : Finset B, ∃ r : Module.Dual k B, r 1 = 1 ∧ ∀ y ∈ T, leftAct r y = r y • (1 : B)

/-- Contraction of the first tensor factor with a functional. -/
def contract (r : Module.Dual k B) : B ⊗[k] B →ₗ[k] B :=
  TensorProduct.lid k B ∘ₗ r.rTensor B

theorem contract_tmul (r : Module.Dual k B) (x y : B) : contract r (x ⊗ₜ y) = r x • y := by
  simp [contract]

theorem leftAct_eq_contract (r : Module.Dual k B) (y : B) :
    letI := (bialgebra (corepresentableBy H ψ)).toCoalgebra
    leftAct r y = contract r (comul (corepresentableBy H ψ) y) := rfl

theorem contract_includeRight_mul (r : Module.Dual k B) (a : B) (t : B ⊗[k] B) :
    contract r ((includeRight : B →ₐ[k] B ⊗[k] B) a * t) = a * contract r t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      contract_tmul, contract_tmul, mul_smul_comm]
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]

theorem contract_includeLeft (r : Module.Dual k B) (x : B) :
    contract r ((includeLeft : B →ₐ[k] B ⊗[k] B) x) = algebraMap k B (r x) := by
  rw [Algebra.TensorProduct.includeLeft_apply, contract_tmul, Algebra.algebraMap_eq_smul_one]

theorem contract_triple (r : Module.Dual k B) (a y b : B) :
    contract r ((includeRight : B →ₐ[k] B ⊗[k] B) a * (includeLeft : B →ₐ[k] B ⊗[k] B) y *
      (includeRight : B →ₐ[k] B ⊗[k] B) b) = a * algebraMap k B (r y) * b := by
  rw [mul_comm _ ((includeRight : B →ₐ[k] B ⊗[k] B) b), ← mul_assoc, ← map_mul,
    contract_includeRight_mul, contract_includeLeft]
  ring

omit [DecidableEq n] in
theorem contract_matrix (r : Module.Dual k B) (U Y V : Matrix n n B) :
    (U.map (includeRight : B →ₐ[k] B ⊗[k] B) * Y.map (includeLeft : B →ₐ[k] B ⊗[k] B) *
        V.map (includeRight : B →ₐ[k] B ⊗[k] B)).map (contract r) =
      U * Y.map (fun y => algebraMap k B (r y)) * V := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Finset.sum_mul, map_sum, contract_triple]

/-- The conjugate `P⁻¹ Q P` of a constant matrix `Q` by the universal matrix `P`. -/
def avgConj (Q : Matrix n n k) : Matrix n n B :=
  (((univMatrix ψ ρ)⁻¹ : GL n B) : Matrix n n B) * Q.map (algebraMap k B) *
    (univMatrix ψ ρ : Matrix n n B)

/-- Averaging the conjugate `P⁻¹ Q P` of a constant matrix with a functional that is a right
integral at its entries gives a matrix commuting with the universal matrix `P`. -/
theorem conj_average (Q : Matrix n n k) (r : Module.Dual k B)
    (hr : ∀ i j, letI := (bialgebra (corepresentableBy H ψ)).toCoalgebra
      leftAct r (avgConj ψ ρ Q i j) = r (avgConj ψ ρ Q i j) • (1 : B)) :
    (((univMatrix ψ ρ)⁻¹ : GL n B) : Matrix n n B) *
        (avgConj ψ ρ Q).map (fun y => algebraMap k B (r y)) *
        (univMatrix ψ ρ : Matrix n n B) =
      (avgConj ψ ρ Q).map (fun y => algebraMap k B (r y)) := by
  set e := corepresentableBy H ψ
  set P := univMatrix ψ ρ
  set X := avgConj ψ ρ Q with hXdef
  have hXP : X = ((P⁻¹ : GL n B) : Matrix n n B) * Q.map (algebraMap k B) * (P : Matrix n n B) :=
    rfl
  have hΔP : (P : Matrix n n B).map (comul e).toRingHom =
      (P : Matrix n n B).map (includeLeft : B →ₐ[k] B ⊗[k] B).toRingHom *
        (P : Matrix n n B).map (includeRight : B →ₐ[k] B ⊗[k] B).toRingHom := by
    have h := congrArg Units.val (univMatrix_comul ψ ρ)
    rw [Units.val_mul] at h
    exact h
  have hΔPinv : ((P⁻¹ : GL n B) : Matrix n n B).map (comul e).toRingHom =
      ((P⁻¹ : GL n B) : Matrix n n B).map (includeRight : B →ₐ[k] B ⊗[k] B).toRingHom *
        ((P⁻¹ : GL n B) : Matrix n n B).map (includeLeft : B →ₐ[k] B ⊗[k] B).toRingHom := by
    have h : Matrix.GeneralLinearGroup.map (comul e).toRingHom P⁻¹ =
        Matrix.GeneralLinearGroup.map (includeRight : B →ₐ[k] B ⊗[k] B).toRingHom P⁻¹ *
          Matrix.GeneralLinearGroup.map (includeLeft : B →ₐ[k] B ⊗[k] B).toRingHom P⁻¹ := by
      rw [map_inv, map_inv, map_inv, univMatrix_comul, mul_inv_rev]
    have h' := congrArg Units.val h
    rw [Units.val_mul] at h'
    exact h'
  have hQ : (Q.map (algebraMap k B)).map (comul e).toRingHom =
      (Q.map (algebraMap k B)).map (includeLeft : B →ₐ[k] B ⊗[k] B).toRingHom := by
    ext i j
    simp only [Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [AlgHom.commutes, AlgHom.commutes]
  have hX : X.map (comul e).toRingHom =
      ((P⁻¹ : GL n B) : Matrix n n B).map (includeRight : B →ₐ[k] B ⊗[k] B) *
        X.map (includeLeft : B →ₐ[k] B ⊗[k] B) *
          (P : Matrix n n B).map (includeRight : B →ₐ[k] B ⊗[k] B) := by
    have h1 : X.map (includeLeft : B →ₐ[k] B ⊗[k] B) =
        X.map (includeLeft : B →ₐ[k] B ⊗[k] B).toRingHom := rfl
    have h2 : ((P⁻¹ : GL n B) : Matrix n n B).map (includeRight : B →ₐ[k] B ⊗[k] B) =
        ((P⁻¹ : GL n B) : Matrix n n B).map (includeRight : B →ₐ[k] B ⊗[k] B).toRingHom := rfl
    have h3 : (P : Matrix n n B).map (includeRight : B →ₐ[k] B ⊗[k] B) =
        (P : Matrix n n B).map (includeRight : B →ₐ[k] B ⊗[k] B).toRingHom := rfl
    rw [h1, h2, h3]
    simp only [hXP, Matrix.map_mul, hΔP, hΔPinv, hQ, Matrix.mul_assoc]
  calc ((P⁻¹ : GL n B) : Matrix n n B) * X.map (fun y => algebraMap k B (r y)) *
        (P : Matrix n n B)
      = (((P⁻¹ : GL n B) : Matrix n n B).map (includeRight : B →ₐ[k] B ⊗[k] B) *
          X.map (includeLeft : B →ₐ[k] B ⊗[k] B) *
            (P : Matrix n n B).map (includeRight : B →ₐ[k] B ⊗[k] B)).map (contract r) :=
        (contract_matrix r _ _ _).symm
    _ = (X.map (comul e).toRingHom).map (contract r) := by rw [hX]
    _ = X.map (fun y => algebraMap k B (r y)) := by
        ext i j
        rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply,
          Algebra.algebraMap_eq_smul_one, ← hr i j]
        rfl

end Averaging

/-! ### Stable complements from local right integrals -/

section Complement

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (ψ : (algSpec (CommRingCat.of k)).obj (op B) ≅ H.X)
  {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation H n)

/-- A constant matrix commuting with the universal matrix intertwines `ρ` with itself. -/
theorem intertwines_of_commute_univ (C : Matrix n n k)
    (hC : C.map (algebraMap k B) * (univMatrix ψ ρ : Matrix n n B) =
      (univMatrix ψ ρ : Matrix n n B) * C.map (algebraMap k B)) :
    Intertwines ρ ρ C := by
  intro S x
  rw [affineMatrix_eq_map ψ ρ S x]
  set f := ((corepresentableBy H ψ).homEquiv.symm x).hom
  have hCf : C.map (algebraMap k S) = (C.map (algebraMap k B)).map f.toRingHom := by
    ext i j
    exact (f.commutes (C i j)).symm
  rw [hCf]
  change _ * (univMatrix ψ ρ : Matrix n n B).map f.toRingHom =
    (univMatrix ψ ρ : Matrix n n B).map f.toRingHom * _
  rw [← Matrix.map_mul, hC, Matrix.map_mul]

omit [DecidableEq n] in
/-- Applying a functional to the entries of a matrix over `B` and multiplying a constant
vector is applying it to the coordinates of the product. -/
theorem map_dual_mulVec (X : Matrix n n B) (r : Module.Dual k B) (v : n → k) :
    X.map r *ᵥ v = fun i => r ((X *ᵥ fun j => algebraMap k B (v j)) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (X i j), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- A vector over `B` all of whose functional images lie in `W` is fixed by a constant
projection onto `W`. -/
theorem mulVec_eq_self_of_forall_dual {W : Submodule k (n → k)} (q : (n → k) →ₗ[k] (n → k))
    (hqW : ∀ w ∈ W, q w = w) (y : n → B)
    (hy : ∀ ℓ : B →ₗ[k] k, (fun i => ℓ (y i)) ∈ W) :
    (LinearMap.toMatrix' q).map (algebraMap k B) *ᵥ y = y := by
  funext i
  refine Unipotent.eq_of_forall_dual k fun ℓ => ?_
  have h := congrFun (linearFunctional_mulVec_rectangular (LinearMap.toMatrix' q) y ℓ) i
  rw [LinearMap.toMatrix'_mulVec, hqW _ (hy ℓ)] at h
  exact h

omit [DecidableEq n] in
/-- If a matrix `M` over `B` carries `W` into vectors whose functional images lie in `W`,
then so does `M Q` on every vector, for a constant matrix `Q` with columns in `W`. -/
theorem forall_dual_mulVec_mem {W : Submodule k (n → k)} (M : Matrix n n B)
    (hM : ∀ w ∈ W, ∀ ℓ : B →ₗ[k] k,
      (fun i => ℓ ((M *ᵥ fun j => algebraMap k B (w j)) i)) ∈ W)
    (Q : Matrix n n k) (hcol : ∀ j, (fun l => Q l j) ∈ W) (z : n → B) (ℓ : B →ₗ[k] k) :
    (fun i => ℓ (((M * Q.map (algebraMap k B)) *ᵥ z) i)) ∈ W := by
  have h : (fun i => ℓ (((M * Q.map (algebraMap k B)) *ᵥ z) i)) =
      ∑ j, fun i => (ℓ ∘ₗ LinearMap.mulLeft k (z j))
        ((M *ᵥ fun l => algebraMap k B (Q l j)) i) := by
    funext i
    simp only [Finset.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Matrix.mulVec,
      dotProduct, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    ring
  rw [h]
  exact Submodule.sum_mem _ fun j _ => hM _ (hcol j) _

/-- Local right integrals give stable complements. -/
theorem exists_isCompl_of_hasLocalRightIntegrals (hint : HasLocalRightIntegrals ψ)
    {W : Submodule k (n → k)} (hW : ρ.IsStableSubspace W) :
    ∃ C, ρ.IsStableSubspace C ∧ IsCompl W C := by
  classical
  obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl W
  set q : (n → k) →ₗ[k] (n → k) := W.projection W' hWW'
  have hqW : ∀ w ∈ W, q w = w := fun w hw => Submodule.projection_apply_of_mem_left hWW' hw
  set Q := LinearMap.toMatrix' q with hQ
  have hcol : ∀ j, (fun l => Q l j) ∈ W := by
    intro j
    have : (fun l => Q l j) = q (Pi.single j 1) := by
      funext l
      rw [hQ, LinearMap.toMatrix'_apply]
    rw [this]
    exact Submodule.projection_apply_mem hWW' _
  set P := univMatrix ψ ρ with hP
  have hstab := (isStableSubspace_iff_univ ψ ρ W).mp hW
  have hstabinv : ∀ w ∈ W, ∀ ℓ : B →ₗ[k] k,
      (fun i => ℓ ((((P⁻¹ : GL n B) : Matrix n n B) *ᵥ fun j => algebraMap k B (w j)) i)) ∈ W := by
    intro w hw ℓ
    have h := hW B ψ.hom⁻¹ w hw ℓ
    have hinv : ρ.affineMatrix B ψ.hom⁻¹ = P⁻¹ := map_inv _ _
    rwa [hinv] at h
  obtain ⟨r, hr1, hr⟩ := hint (Finset.univ.image fun ij : n × n => avgConj ψ ρ Q ij.1 ij.2)
  set π : Matrix n n k := (avgConj ψ ρ Q).map r with hπ
  have hπB : π.map (algebraMap k B) =
      (avgConj ψ ρ Q).map (fun y => algebraMap k B (r y)) := rfl
  have hcomm : π.map (algebraMap k B) * (P : Matrix n n B) =
      (P : Matrix n n B) * π.map (algebraMap k B) := by
    have h := conj_average ψ ρ Q r fun i j =>
      hr _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    rw [← hπB] at h
    calc π.map (algebraMap k B) * (P : Matrix n n B)
        = (P : Matrix n n B) * (((P⁻¹ : GL n B) : Matrix n n B) * π.map (algebraMap k B) *
            (P : Matrix n n B)) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      _ = (P : Matrix n n B) * π.map (algebraMap k B) := by rw [h]
  have hX : ∀ v : n → k, (avgConj ψ ρ Q *ᵥ fun j => algebraMap k B (v j)) =
      (((P⁻¹ : GL n B) : Matrix n n B) * Q.map (algebraMap k B)) *ᵥ
        ((P : Matrix n n B) *ᵥ fun j => algebraMap k B (v j)) := by
    intro v
    rw [Matrix.mulVec_mulVec]
    rfl
  have hr1' : ∀ c : k, r (algebraMap k B c) = c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hr1, smul_eq_mul, mul_one]
  have hfix : ∀ w ∈ W, π *ᵥ w = w := by
    intro w hw
    rw [hπ, map_dual_mulVec, hX, ← Matrix.mulVec_mulVec,
      mulVec_eq_self_of_forall_dual q hqW _ (hstab w hw), Matrix.mulVec_mulVec, Units.inv_mul,
      Matrix.one_mulVec]
    funext i
    exact hr1' (w i)
  have hmem : ∀ v, π *ᵥ v ∈ W := by
    intro v
    rw [hπ, map_dual_mulVec, hX]
    exact forall_dual_mulVec_mem _ hstabinv Q hcol _ r
  let f : (n → k) →ₗ[k] W := (Matrix.toLin' π).codRestrict W hmem
  have hf : ∀ x : W, f x = x := fun x => Subtype.ext (hfix x x.2)
  refine ⟨LinearMap.ker f, ?_, LinearMap.isCompl_of_proj hf⟩
  have hker : LinearMap.ker f = (⊥ : Submodule k (n → k)).comap π.mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_bot, f,
      Matrix.mulVecLin_apply]
    exact Subtype.ext_iff
  rw [hker]
  exact (isStableSubspace_bot ρ).comap (intertwines_of_commute_univ ψ ρ π hcomm)

end Complement

/-! ### The representation attached to multiplicative matrix coefficients

The following lemmas identify the universal matrix of the representation `toGLHom` built from
multiplicative matrix coefficients `M` with `M` itself. -/

section Model

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) {B : CommAlgCat.{u} R}
  (j : (algSpec R).obj (op B) ≅ G.X)

theorem yonedaGrp_preimage_hom_hom_eq {X Y : Grp (Over (Spec R))}
    (φ : yonedaGrp.obj X ⟶ yonedaGrp.obj Y) :
    (yonedaGrpFullyFaithful.preimage φ).hom.hom = φ.app (op X.X) (𝟙 X.X) := by
  conv_rhs => rw [← yonedaGrpFullyFaithful.map_preimage φ]
  exact (Category.id_comp _).symm

theorem modelIso_hom_hom_hom_eq : (modelIso G j).hom.hom.hom = j.hom := by
  change (yonedaGrpFullyFaithful.preimage _).hom.hom = _
  rw [yonedaGrp_preimage_hom_hom_eq]
  exact Category.id_comp j.hom

set_option backward.isDefEq.respectTransparency false in
theorem modelIso_inv_hom_hom_eq : (modelIso G j).inv.hom.hom = j.inv := by
  rw [← cancel_mono j.hom, Iso.inv_hom_id, ← modelIso_hom_hom_hom_eq, ← Grp.comp_hom_hom,
    Iso.inv_hom_id]
  rfl

theorem affinePointsEquiv_comp_inv_eq (S : CommAlgCat R) (x : (algSpec R).obj (op S) ⟶ G.X) :
    Corepresented.affinePointsEquiv G.affinePointFunctor (corepresentableBy G j) S
      (x ≫ j.inv) = x := by
  rw [Corepresented.affinePointsEquiv_apply]
  change (algSpec R).map (algSpec.fullyFaithful.preimage (x ≫ j.inv)).unop.op ≫ j.hom = x
  rw [Quiver.Hom.op_unop, algSpec.fullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

variable {N : ℕ} (M : Matrix (Fin N) (Fin N) B)
  (hcomul : ∀ i j', comul (corepresentableBy G j) (M i j') = ∑ l, M i l ⊗ₜ[R] M l j')
  (hcounit : ∀ i j', counit (corepresentableBy G j) (M i j') =
    (1 : Matrix (Fin N) (Fin N) R) i j')

/-- The matrix representation of `G` attached to multiplicative matrix coefficients. -/
abbrev coeffRep : MatrixRepresentation G (Fin N) :=
  (modelIso G j).inv ≫ toGLHom (corepresentableBy G j) M hcomul hcounit

/-- Its matrices are the matrix coefficients evaluated at the classifying algebra map. -/
theorem coeffRep_affineMatrix_apply (S : CommAlgCat R) (x : (algSpec R).obj (op S) ⟶ G.X)
    (i j' : Fin N) :
    ((coeffRep G j M hcomul hcounit).affineMatrix S x : Matrix (Fin N) (Fin N) S) i j' =
      ((corepresentableBy G j).homEquiv.symm x).hom (M i j') := by
  rw [MatrixRepresentation.affineMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    modelIso_inv_hom_hom_eq]
  have h := Corepresented.groupSchemeMap_affinePoints (corepresentableBy G j)
    (GeneralLinear.corepresentableBy (Fin N) R) (toGL (corepresentableBy G j) M hcomul hcounit)
    (x ≫ j.inv)
  rw [affinePointsEquiv_comp_inv_eq] at h
  have h2 := congrArg (fun A : (GeneralLinear.functor (Fin N) R).obj S =>
    ((show GL (Fin N) S from A) : Matrix (Fin N) (Fin N) S) i j') h
  exact h2

set_option backward.isDefEq.respectTransparency false in
/-- The classifying algebra map of the universal point is the identity. -/
theorem homEquiv_symm_hom : (corepresentableBy G j).homEquiv.symm j.hom = 𝟙 B := by
  rw [Equiv.symm_apply_eq]
  change j.hom = (algSpec R).map (𝟙 B).op ≫ j.hom
  rw [op_id, CategoryTheory.Functor.map_id, Category.id_comp]

end Model

/-! ### Local right integrals from stable complements -/

section Integrals

open Chevalley

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (ψ : (algSpec (CommRingCat.of k)).obj (op B) ≅ H.X)

/-- The universal matrix of the representation attached to matrix coefficients `M` is `M`. -/
theorem univMatrix_coeffRep {N : ℕ} (M : Matrix (Fin N) (Fin N) B) (hcomul) (hcounit) :
    (univMatrix ψ (coeffRep H ψ M hcomul hcounit) : Matrix (Fin N) (Fin N) B) = M := by
  ext i j
  rw [coeffRep_affineMatrix_apply, homEquiv_symm_hom]
  rfl

theorem dual_algebraMap (ℓ : B →ₗ[k] k) (c : k) : ℓ (algebraMap k B c) = c * ℓ 1 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]

/-- If every representation of `H` has stable complements, the coordinate algebra has local
right integrals. -/
theorem hasLocalRightIntegrals_of_exists_isCompl
    (h : ∀ (N : ℕ) (ρ : MatrixRepresentation H (Fin N)) (W : Submodule k (Fin N → k)),
      ρ.IsStableSubspace W → ∃ C, ρ.IsStableSubspace C ∧ IsCompl W C) :
    HasLocalRightIntegrals ψ := by
  classical
  let e := corepresentableBy H ψ
  let := bialgebra e
  dsimp only [HasLocalRightIntegrals]
  intro T
  let V : Submodule k B := regularSpan (insert 1 T)
  have hV : ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V :=
    fun f _ hv => rightAct_mem_regularSpan _ f hv
  have h1V : (1 : B) ∈ V := subset_regularSpan _ (Finset.mem_insert_self _ _)
  let N := Module.finrank k V
  let b : Module.Basis (Fin N) k V := Module.finBasis k V
  let M := subspaceMatrix V b
  let ρ : MatrixRepresentation H (Fin N) :=
    coeffRep H ψ M (comul_subspaceMatrix V b hV) (counit_subspaceMatrix V b)
  have hP : (univMatrix ψ ρ : Matrix (Fin N) (Fin N) B) = M := univMatrix_coeffRep ψ M _ _
  -- The coordinates of `1` form a fixed vector.
  let u : Fin N → k := fun i => extendedCoord V b i 1
  have hu1 : ∑ i, u i • (b i : B) = 1 := basis_expand V b h1V
  have hu0 : u ≠ 0 := by
    intro h0
    apply Unipotent.one_ne_zero' k B
    rw [← hu1, h0]
    simp
  have hrowu : ∀ i, ∑ j, u j • M i j = u i • (1 : B) := by
    intro i
    have hleft1 : leftAct (extendedCoord V b i) (1 : B) = u i • (1 : B) := by
      rw [leftAct_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    rw [← hleft1, ← hu1, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    rfl
  have hfixu : (M *ᵥ fun j => algebraMap k B (u j)) = fun i => algebraMap k B (u i) := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    rw [Algebra.algebraMap_eq_smul_one (u i), ← hrowu i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have hcoef : ∀ (ℓ : B →ₗ[k] k) (v : Fin N → k), coefficientMap ρ B ψ.hom ℓ v =
      fun i => ℓ ((M *ᵥ fun j => algebraMap k B (v j)) i) := by
    intro ℓ v
    funext i
    change ℓ (((univMatrix ψ ρ : Matrix (Fin N) (Fin N) B) *ᵥ _) i) = _
    rw [hP]
  have hcoefu : ∀ ℓ : B →ₗ[k] k, coefficientMap ρ B ψ.hom ℓ u = ℓ 1 • u := by
    intro ℓ
    rw [hcoef, hfixu]
    funext i
    rw [dual_algebraMap, Pi.smul_apply, smul_eq_mul, mul_comm]
  -- The line through `u` is stable; take a stable complement.
  have hUstab : ρ.IsStableSubspace (k ∙ u) := by
    rw [isStableSubspace_iff_univ ψ ρ]
    intro v hv ℓ
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have h1 := (coefficientMap ρ B ψ.hom ℓ).map_smul a u
    rw [hcoefu] at h1
    refine Submodule.mem_span_singleton.mpr ⟨a * ℓ 1, ?_⟩
    change _ = coefficientMap ρ B ψ.hom ℓ (a • u)
    rw [h1, smul_smul]
  obtain ⟨C, hC, hcompl⟩ := h N ρ _ hUstab
  -- A functional that is `1` on `u` and vanishes on the complement.
  let c : Module.Dual k (Fin N → k) :=
    (LinearEquiv.toSpanNonzeroSingleton k (Fin N → k) u hu0).symm.toLinearMap ∘ₗ
      (k ∙ u).projectionOnto C hcompl
  have hcu : c u = 1 := by
    simp only [c, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Submodule.projectionOnto_apply_of_mem_left hcompl (Submodule.mem_span_singleton_self u),
      LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  have hcC : ∀ w ∈ C, c w = 0 := by
    intro w hw
    simp only [c, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Submodule.projectionOnto_apply_of_mem_right hcompl hw, map_zero]
  let cv : Fin N → k := fun i => c (fun j => if i = j then 1 else 0)
  have hc_expand : ∀ x : Fin N → k, c x = ∑ i, x i * cv i := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ c x]
    rfl
  -- The functional is invariant: `∑ i, cv i • M i j = cv j • 1`.
  have hclaim : ∀ v : Fin N → k,
      ∑ i, cv i • (M *ᵥ fun j => algebraMap k B (v j)) i = algebraMap k B (c v) := by
    intro v
    refine Unipotent.eq_of_forall_dual k fun ℓ => ?_
    rw [map_sum, dual_algebraMap]
    simp only [map_smul, smul_eq_mul]
    have key : c (coefficientMap ρ B ψ.hom ℓ v) = c v * ℓ 1 := by
      have hv : v ∈ (k ∙ u) ⊔ C := hcompl.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_add, map_smul, map_add, map_add, map_smul, map_smul, hcoefu,
        hcC (coefficientMap ρ B ψ.hom ℓ z) (hC B ψ.hom z hz ℓ), hcC z hz, map_smul, hcu]
      simp only [smul_eq_mul]
      ring
    rw [← key, hc_expand, hcoef]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hcol : ∀ j, ∑ i, cv i • M i j = cv j • (1 : B) := by
    intro j
    have h1 := hclaim (fun l => if j = l then 1 else 0)
    have hMj : (M *ᵥ fun l => algebraMap k B (if j = l then 1 else 0)) = fun i => M i j := by
      funext i
      simp [Matrix.mulVec, dotProduct, apply_ite]
    rw [hMj] at h1
    rw [h1, Algebra.algebraMap_eq_smul_one]
  -- The integral is the corresponding combination of coordinate functionals.
  let r : Module.Dual k B := ∑ i, cv i • extendedCoord V b i
  have hrb : ∀ j, r (b j : B) = cv j := by
    intro j
    simp [r, LinearMap.sum_apply, extendedCoord_basis, Matrix.one_apply]
  have hr1 : r 1 = 1 := by
    rw [← hcu, hc_expand]
    simp only [r, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hlin : ∀ a : B, leftAct r a = ∑ i, cv i • leftAct (extendedCoord V b i) a := by
    intro a
    apply Unipotent.eq_of_forall_dual k
    intro g
    rw [apply_leftAct, map_sum]
    simp only [r, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, apply_leftAct]
  have hleft : ∀ j, leftAct r (b j : B) = cv j • (1 : B) := by
    intro j
    rw [hlin, ← hcol j]
    rfl
  refine ⟨r, hr1, fun y hy => ?_⟩
  have hyV : y ∈ V := subset_regularSpan _ (Finset.mem_insert_of_mem hy)
  rw [← basis_expand V b hyV, map_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, hleft j, hrb j, smul_smul, smul_eq_mul]

/-- **Linear reductivity criterion.** `H` is linearly reductive (the simple stable subspaces
of every representation span) exactly when the coordinate algebra of any presentation has
local right integrals. -/
theorem linearlyReductive_iff_hasLocalRightIntegrals :
    (∀ (N : ℕ) (ρ : MatrixRepresentation H (Fin N)), sSup (simpleStable ρ) = ⊤) ↔
      HasLocalRightIntegrals ψ :=
  ⟨fun h => hasLocalRightIntegrals_of_exists_isCompl ψ fun N ρ _ hW =>
      exists_isCompl_of_sSup_simpleStable ρ (h N ρ) hW,
    fun h _ ρ => sSup_simpleStable_eq_top ρ fun _ hW =>
      exists_isCompl_of_hasLocalRightIntegrals ψ ρ h hW⟩

end Integrals

end Langlands.GroupScheme.LinearReductivity
