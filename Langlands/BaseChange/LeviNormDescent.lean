import Langlands.BaseChange.PseudoCoefficient
import Langlands.LinearAlgebra.JordanChevalleyFunctoriality
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! # Cyclic norms and block centralizers -/

namespace Langlands.BaseChange

open Langlands.GeneralLinear
open _root_.Polynomial

universe u v

private theorem intertwiner_eq_zero {R : Type u} [Field R] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) R) (C : Matrix (Fin b) (Fin b) R)
    (X : Matrix (Fin a) (Fin b) R) (h : A * X = X * C)
    (hAC : IsCoprime A.charpoly C.charpoly) : X = 0 := by
  have hLin : A.mulVecLin.comp X.mulVecLin = X.mulVecLin.comp C.mulVecLin := by
    simpa only [Matrix.mulVecLin_mul] using congrArg Matrix.mulVecLin h
  have hA : aeval A.mulVecLin A.charpoly = 0 := by
    rw [← Matrix.charpoly_mulVecLin]
    exact LinearMap.aeval_self_charpoly _
  have hC : aeval C.mulVecLin C.charpoly = 0 := by
    rw [← Matrix.charpoly_mulVecLin]
    exact LinearMap.aeval_self_charpoly _
  have hzero : (aeval A.mulVecLin C.charpoly).comp X.mulVecLin = 0 := by
    rw [Langlands.LinearAlgebra.aeval_intertwines X.mulVecLin hLin, hC, LinearMap.comp_zero]
  obtain ⟨p, q, hpq⟩ := hAC
  have hOne : aeval A.mulVecLin q * aeval A.mulVecLin C.charpoly = 1 := by
    have he := congrArg (aeval A.mulVecLin) hpq
    simpa only [map_add, map_mul, map_one, hA, mul_zero, zero_add] using he
  apply Matrix.toLin'.injective
  change X.mulVecLin = (0 : Matrix (Fin a) (Fin b) R).mulVecLin
  rw [show (0 : Matrix (Fin a) (Fin b) R).mulVecLin = 0 by exact Matrix.toLin'.map_zero]
  calc
    X.mulVecLin = (1 : Module.End R (Fin a → R)).comp X.mulVecLin :=
      (LinearMap.id_comp _).symm
    _ = 0 := by
      rw [← hOne, Module.End.mul_eq_comp, LinearMap.comp_assoc, hzero, LinearMap.comp_zero]

section Blocks

variable {R : Type u} [Field R] {n : ℕ} (B : BlockShape n)

private theorem commuting_offBlock_eq_zero (m : B.Levi R) (g : GeneralLinear n R)
    (h : Commute (B.leviEmbedding R m) g) {i j : Fin B.length}
    (hc : IsCoprime (m i).val.charpoly (m j).val.charpoly) :
    g.val.submatrix (B.index i) (B.index j) = 0 := by
  apply intertwiner_eq_zero (m i).val (m j).val _ _ hc
  have hentries (a : Fin (B.size i)) (b : Fin (B.size j)) :
      (∑ k : Fin n, B.leviEmbedding R m (B.index i a) k * g k (B.index j b)) =
        ∑ k : Fin n, g (B.index i a) k * B.leviEmbedding R m k (B.index j b) :=
    congrArg (fun z : GeneralLinear n R => z (B.index i a) (B.index j b)) h.eq
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  specialize hentries a b
  rw [← Equiv.sum_comp B.indexEquiv, ← Equiv.sum_comp B.indexEquiv] at hentries
  simp only [← Finset.univ_sigma_univ, Finset.sum_sigma] at hentries
  rw [Fintype.sum_eq_single i, Fintype.sum_eq_single j] at hentries
  · change
      (∑ t : Fin (B.size i), B.leviEmbedding R m (B.index i a) (B.index i t) *
        g (B.index i t) (B.index j b)) =
      ∑ t : Fin (B.size j), g (B.index i a) (B.index j t) *
        B.leviEmbedding R m (B.index j t) (B.index j b) at hentries
    simpa only [BlockShape.leviEmbedding_apply_same] using hentries
  · intro k hk
    apply Finset.sum_eq_zero
    intro t _
    change g (B.index i a) (B.index k t) * B.leviEmbedding R m (B.index k t) (B.index j b) = 0
    rw [B.leviEmbedding_apply_ne R m t b hk, mul_zero]
  · intro k hk
    apply Finset.sum_eq_zero
    intro t _
    change B.leviEmbedding R m (B.index i a) (B.index k t) * g (B.index k t) (B.index j b) = 0
    rw [B.leviEmbedding_apply_ne R m a t hk.symm, zero_mul]

/-- An invertible matrix with all off-diagonal blocks zero belongs to the standard Levi. -/
theorem mem_leviSubgroup_iff_offBlock_eq_zero (g : GeneralLinear n R) :
    g ∈ B.leviSubgroup R ↔ ∀ (i j : Fin B.length) (a : Fin (B.size i))
      (b : Fin (B.size j)), i ≠ j → g (B.index i a) (B.index j b) = 0 := by
  constructor
  · rintro ⟨m, rfl⟩ i j a b hij
    exact B.leviEmbedding_apply_ne R m a b hij
  · intro h
    let p : B.parabolic R := ⟨g, (B.mem_parabolic_iff R g).2 (fun i j a b hji =>
      h i j a b (ne_of_gt hji))⟩
    refine ⟨B.leviProjection R p, ?_⟩
    ext x y
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
    change B.leviEmbedding R (B.leviProjection R p) (B.index i a) (B.index j b) =
      g (B.index i a) (B.index j b)
    by_cases hij : i = j
    · subst j
      rw [BlockShape.leviEmbedding_apply_same, BlockShape.leviProjection_apply]
    · rw [B.leviEmbedding_apply_ne R _ a b hij, h i j a b hij]

/-- Pairwise coprime block characteristic polynomials force the centralizer into the Levi. -/
theorem mem_leviSubgroup_of_commute (m : B.Levi R)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly)
    {g : GeneralLinear n R} (h : Commute (B.leviEmbedding R m) g) :
    g ∈ B.leviSubgroup R := by
  refine (mem_leviSubgroup_iff_offBlock_eq_zero B g).2 fun i j a b hij => ?_
  exact congrArg (fun X : Matrix (Fin (B.size i)) (Fin (B.size j)) R => X a b)
    (commuting_offBlock_eq_zero B m g h (hm hij))

/-- The ordinary centralizer of a block diagonal element with pairwise coprime
characteristic polynomials lies in the standard Levi. -/
theorem glCentralizer_le_leviSubgroup (m : B.Levi R)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly) :
    glCentralizer (B.leviEmbedding R m) ≤ B.leviSubgroup R := by
  intro g hg
  rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hg
  exact mem_leviSubgroup_of_commute B m hm hg.symm

end Blocks

section BaseChange

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
variable {n l : ℕ} (B : BlockShape n) {σ : E ≃ₐ[F] E}

/-- Scalar extension on the ambient group carries a Levi element to the extension of its blocks. -/
private theorem baseChange_leviEmbedding (m : B.Levi F) :
    baseChange F E n (B.leviEmbedding F m) =
      B.leviEmbedding E (fun i => baseChange F E (B.size i) (m i)) := by
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change algebraMap F E (B.leviEmbedding F m (B.index i a) (B.index j b)) =
    B.leviEmbedding E (fun k => baseChange F E (B.size k) (m k)) (B.index i a) (B.index j b)
  by_cases hij : i = j
  · subst j
    rw [BlockShape.leviEmbedding_apply_same, BlockShape.leviEmbedding_apply_same,
      baseChange_apply_apply]
  · rw [B.leviEmbedding_apply_ne F m a b hij, B.leviEmbedding_apply_ne E _ a b hij, map_zero]

private theorem pairwise_charpoly_baseChange (m : B.Levi F)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly) :
    Pairwise fun i j => IsCoprime (baseChange F E (B.size i) (m i)).val.charpoly
      (baseChange F E (B.size j) (m j)).val.charpoly := by
  intro i j hij
  change IsCoprime (((m i).val.map (algebraMap F E)).charpoly)
    (((m j).val.map (algebraMap F E)).charpoly)
  rw [Matrix.charpoly_map, Matrix.charpoly_map]
  exact (hm hij).map (Polynomial.mapRingHom (algebraMap F E))

/-- The cyclic norm of a block diagonal element is the block diagonal of the cyclic norms. -/
private theorem cyclicNorm_leviEmbedding (σ : E ≃ₐ[F] E) (l : ℕ) (m : B.Levi E) :
    cyclicNorm σ l (B.leviEmbedding E m) =
      B.leviEmbedding E (fun i => cyclicNorm σ l (m i)) := by
  induction l with
  | zero => simp only [cyclicNorm_zero, ← Pi.one_def, map_one]
  | succ l ih =>
    rw [cyclicNorm_succ, ih, entrywiseAut_leviEmbedding, ← map_mul]
    apply congrArg (B.leviEmbedding E)
    funext i
    simp only [Pi.mul_apply, leviAut_apply, cyclicNorm_succ]

/-- An exact norm equality with a block diagonal ordinary element puts the twisted
representative in the Levi, with exact norm equality in each block. -/
theorem exists_levi_of_cyclicNorm_eq (hσ : σ ^ l = 1)
    (m : B.Levi F) (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly)
    {δ : GeneralLinear n E}
    (hn : cyclicNorm σ l δ = baseChange F E n (B.leviEmbedding F m)) :
    ∃ d : B.Levi E, δ = B.leviEmbedding E d ∧
      ∀ i, cyclicNorm σ l (d i) = baseChange F E (B.size i) (m i) := by
  have hc : entrywiseAut σ n (cyclicNorm σ l δ) = cyclicNorm σ l δ := by
    rw [hn, entrywiseAut_baseChange]
  rw [entrywiseAut_cyclicNorm, hσ, entrywiseAut_one_apply] at hc
  have hcomm : Commute (cyclicNorm σ l δ) δ := by
    have h' := congrArg (fun y => δ * y) hc
    simpa only [Commute, SemiconjBy, ← mul_assoc, mul_inv_cancel, one_mul] using h'
  have hmE := pairwise_charpoly_baseChange (E := E) B m hm
  have hδ : δ ∈ B.leviSubgroup E := by
    rw [hn, baseChange_leviEmbedding] at hcomm
    exact mem_leviSubgroup_of_commute B _ hmE hcomm
  obtain ⟨d, hd⟩ := hδ
  refine ⟨d, hd.symm, ?_⟩
  rw [← hd, cyclicNorm_leviEmbedding, baseChange_leviEmbedding] at hn
  exact congrFun (B.leviEmbedding_injective E hn)

/-- Blockwise association gives ambient association for the same cyclic norm. -/
theorem isNormAssociated_leviEmbedding_of_forall (m : B.Levi F) (d : B.Levi E)
    (h : ∀ i, IsNormAssociated σ l (d i) (m i)) :
    IsNormAssociated σ l (B.leviEmbedding E d) (B.leviEmbedding F m) := by
  classical
  choose x hx using h
  refine ⟨B.leviEmbedding E x, ?_⟩
  rw [cyclicNorm_leviEmbedding, baseChange_leviEmbedding, ← map_inv, ← map_mul, ← map_mul]
  apply congrArg (B.leviEmbedding E)
  funext i
  exact hx i

/-- Norm membership of a block diagonal element with pairwise coprime characteristic
polynomials is equivalent to norm membership in every block. -/
theorem isNorm_leviEmbedding_iff (hσ : σ ^ l = 1)
    (m : B.Levi F) (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly) :
    IsNorm σ l (B.leviEmbedding F m) ↔ ∀ i, IsNorm σ l (m i) := by
  constructor
  · rintro ⟨δ, x, hx⟩ i
    have hn : cyclicNorm σ l (x⁻¹ * δ * entrywiseAut σ n x) =
        baseChange F E n (B.leviEmbedding F m) := by
      rw [cyclicNorm_twistedConj, hσ, entrywiseAut_one_apply, hx]
    obtain ⟨d, _, hd⟩ := exists_levi_of_cyclicNorm_eq B hσ m hm hn
    exact ⟨d i, 1, by simpa only [inv_one, one_mul, mul_one] using hd i⟩
  · intro h
    classical
    choose d hd using h
    exact ⟨B.leviEmbedding E d, isNormAssociated_leviEmbedding_of_forall B m d hd⟩

end BaseChange

end Langlands.BaseChange
