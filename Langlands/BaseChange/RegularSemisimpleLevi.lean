import Langlands.Group.GL.TwoBlockShape
import Langlands.JacquetLanglands.RegularElliptic
import Langlands.LinearAlgebra.JordanChevalleyFunctoriality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # A proper two-block Levi for a nonelliptic regular semisimple element -/

namespace Langlands.BaseChange

open Langlands.GeneralLinear Langlands.JacquetLanglands
open Langlands.ProductLeviChamber (twoBlock twoBlock_index_val)
open _root_.Polynomial

universe u v

private theorem charpoly_dvd_of_separable_of_aeval_eq_zero
    {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (A : Module.End F V) {p : F[X]} (hp : p ≠ 0) (hs : A.charpoly.Separable)
    (h : aeval A p = 0) : A.charpoly ∣ p := by
  classical
  let L := AlgebraicClosure F
  let A' := A.baseChange L
  apply (map_dvd_map' (algebraMap F L)).mp
  rw [← LinearMap.charpoly_baseChange]
  have hAnn : aeval A' (p.map (algebraMap F L)) = 0 := by
    rw [aeval_map_algebraMap]
    change aeval (Module.End.baseChangeHom F L V A) p = 0
    rw [aeval_algHom_apply, h, map_zero]
  have hmono : A'.charpoly.Monic := A'.charpoly_monic
  have hsep : A'.charpoly.Separable := by
    rw [LinearMap.charpoly_baseChange]
    exact hs.map
  have hmap : p.map (algebraMap F L) ≠ 0 := fun e => hp ((Polynomial.map_eq_zero _).mp e)
  rw [(IsAlgClosed.splits A'.charpoly).eq_prod_roots_of_monic hmono,
    Multiset.prod_X_sub_C_dvd_iff_le_roots hmap]
  apply (Multiset.le_iff_subset (Polynomial.nodup_roots hsep)).2
  intro x hx
  have hroot := (mem_roots hmono.ne_zero).1 hx
  obtain ⟨w, hw⟩ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly A' x).2 hroot |>.exists_hasEigenvector
  apply (mem_roots hmap).2
  have hsmul := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap F L)) hw
  rw [hAnn, LinearMap.zero_apply] at hsmul
  exact (smul_eq_zero.mp hsmul.symm).resolve_right hw.2

private theorem aeval_ker_invariant {F : Type u} [Field F] {V : Type v}
    [AddCommGroup V] [Module F V] (A : Module.End F V) (p : F[X]) :
    ∀ x ∈ LinearMap.ker (aeval A p), A x ∈ LinearMap.ker (aeval A p) := by
  intro x hx
  have h := LinearMap.congr_fun (Langlands.LinearAlgebra.aeval_intertwines A rfl p) x
  change aeval A p (A x) = A (aeval A p x) at h
  rw [LinearMap.mem_ker] at hx ⊢
  rw [h, hx, map_zero]

private theorem aeval_restrict_ker_eq_zero {F : Type u} [Field F] {V : Type v}
    [AddCommGroup V] [Module F V] (A : Module.End F V) (p : F[X]) :
    aeval (A.restrict (aeval_ker_invariant A p)) p = 0 := by
  let U := LinearMap.ker (aeval A p)
  let A₁ : Module.End F U := A.restrict (aeval_ker_invariant A p)
  have h : (aeval A p).comp U.subtype = U.subtype.comp (aeval A₁ p) :=
    Langlands.LinearAlgebra.aeval_intertwines U.subtype rfl p
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (LinearMap.congr_fun h x).symm.trans x.property

/-- A factorization into two positive-degree monic factors gives a standard two-block
representative with the prescribed characteristic polynomials. -/
theorem exists_twoBlock_of_charpoly_mul {F : Type u} [Field F] {n : ℕ}
    (γ : GeneralLinear n F) (hreg : IsRegularSemisimple γ) {p q : F[X]}
    (hp : p.Monic) (hq : q.Monic) (hfac : γ.val.charpoly = p * q)
    (hk : 0 < p.natDegree) (hkn : p.natDegree < n) :
    let B := twoBlock n p.natDegree hk hkn
    ∃ (g : GeneralLinear n F) (m : B.Levi F),
      g⁻¹ * γ * g = B.leviEmbedding F m ∧
      (m (0 : Fin 2)).val.charpoly = p ∧ (m (1 : Fin 2)).val.charpoly = q := by
  classical
  let A := γ.val.mulVecLin
  have hfacA : A.charpoly = p * q := (Matrix.charpoly_mulVecLin _).trans hfac
  have hs : (p * q).Separable := hfac ▸ hreg
  let U := LinearMap.ker (aeval A p)
  let W := LinearMap.ker (aeval A q)
  have hc : IsCompl U W := by
    refine ⟨disjoint_ker_aeval_of_isCoprime A hs.isCoprime, codisjoint_iff.mpr ?_⟩
    change LinearMap.ker (aeval A p) ⊔ LinearMap.ker (aeval A q) = ⊤
    rw [sup_ker_aeval_eq_ker_aeval_mul_of_coprime A hs.isCoprime, ← hfacA,
      LinearMap.aeval_self_charpoly, LinearMap.ker_zero]
  let A₁ : Module.End F U := A.restrict (aeval_ker_invariant A p)
  let A₂ : Module.End F W := A.restrict (aeval_ker_invariant A q)
  let e := Submodule.prodEquivOfIsCompl U W hc
  have he : A.comp e.toLinearMap = e.toLinearMap.comp (A₁.prodMap A₂) := by
    apply LinearMap.ext
    intro x
    change A ((x.1 : Fin n → F) + (x.2 : Fin n → F)) = A ↑x.1 + A ↑x.2
    exact map_add A _ _
  have heConj : e.conj (A₁.prodMap A₂) = A := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply]
    exact (LinearMap.congr_fun he y).symm
  have hprod : A₁.charpoly * A₂.charpoly = p * q := by
    rw [← LinearMap.charpoly_prodMap, ← e.charpoly_conj, heConj, hfacA]
  have hprodSep : (A₁.charpoly * A₂.charpoly).Separable := hprod ▸ hs
  have hd₁ : A₁.charpoly ∣ p :=
    charpoly_dvd_of_separable_of_aeval_eq_zero A₁ hp.ne_zero hprodSep.of_mul_left
      (aeval_restrict_ker_eq_zero A p)
  have hd₂ : A₂.charpoly ∣ q :=
    charpoly_dvd_of_separable_of_aeval_eq_zero A₂ hq.ne_zero hprodSep.of_mul_right
      (aeval_restrict_ker_eq_zero A q)
  have hdeg := congrArg natDegree hprod
  rw [A₁.charpoly_monic.natDegree_mul A₂.charpoly_monic, hp.natDegree_mul hq] at hdeg
  have hle₁ := natDegree_le_of_dvd hd₁ hp.ne_zero
  have hle₂ := natDegree_le_of_dvd hd₂ hq.ne_zero
  have hcp₁ : A₁.charpoly = p :=
    (eq_of_monic_of_dvd_of_natDegree_le A₁.charpoly_monic hp hd₁ (by omega)).symm
  have hcp₂ : A₂.charpoly = q :=
    (eq_of_monic_of_dvd_of_natDegree_le A₂.charpoly_monic hq hd₂ (by omega)).symm
  have hsum : p.natDegree + q.natDegree = n := by
    rw [← hp.natDegree_mul hq, ← hfac, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let B := twoBlock n p.natDegree hk hkn
  have hu : Module.finrank F U = B.size (0 : Fin 2) := by
    change Module.finrank F U = p.natDegree
    rw [← A₁.charpoly_natDegree, hcp₁]
  have hw : Module.finrank F W = B.size (1 : Fin 2) := by
    change Module.finrank F W = n - p.natDegree
    rw [← A₂.charpoly_natDegree, hcp₂]
    omega
  let b₁ := (Module.finBasis F U).reindex (finCongr hu)
  let b₂ := (Module.finBasis F W).reindex (finCongr hw)
  let M₁ := LinearMap.toMatrix b₁ b₁ A₁
  let M₂ := LinearMap.toMatrix b₂ b₂ A₂
  have hc₁ : M₁.charpoly = p := (LinearMap.charpoly_toMatrix _ _).trans hcp₁
  have hc₂ : M₂.charpoly = q := (LinearMap.charpoly_toMatrix _ _).trans hcp₂
  have hcoeff : (p * q).coeff 0 ≠ 0 := by
    intro hzero
    apply γ.det_ne_zero
    rw [Matrix.det_eq_sign_charpoly_coeff, hfac, hzero, mul_zero]
  rw [Polynomial.mul_coeff_zero] at hcoeff
  have hdet₁ : M₁.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hc₁]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (left_ne_zero_of_mul hcoeff)
  have hdet₂ : M₂.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hc₂]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (right_ne_zero_of_mul hcoeff)
  let g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero M₁ hdet₁
  let g₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero M₂ hdet₂
  let m : B.Levi F := Fin.cases g₁ fun j => by
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact g₂
  have hm₁ : m (0 : Fin 2) = g₁ := rfl
  have hm₂ : m (1 : Fin 2) = g₂ := rfl
  have hsize : B.size (0 : Fin 2) + B.size (1 : Fin 2) = n := by
    change p.natDegree + (n - p.natDegree) = n
    omega
  let ρ : Fin (B.size (0 : Fin 2)) ⊕ Fin (B.size (1 : Fin 2)) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr hsize)
  have hρ₁ (i : Fin (B.size (0 : Fin 2))) : ρ (Sum.inl i) = B.index (0 : Fin 2) i := by
    apply Fin.ext
    exact (zero_add (i : ℕ)).symm.trans
      (twoBlock_index_val n p.natDegree hk hkn (0 : Fin 2) i).symm
  have hρ₂ (i : Fin (B.size (1 : Fin 2))) : ρ (Sum.inr i) = B.index (1 : Fin 2) i := by
    apply Fin.ext
    exact (twoBlock_index_val n p.natDegree hk hkn (1 : Fin 2) i).symm
  let b := (b₁.prod b₂).map e
  let c := b.reindex ρ
  let c₀ := Pi.basisFun F (Fin n)
  let g : GeneralLinear n F :=
    ⟨c₀.toMatrix c, c.toMatrix c₀, c₀.toMatrix_mul_toMatrix_flip c,
      c.toMatrix_mul_toMatrix_flip c₀⟩
  have hMatrix : LinearMap.toMatrix b b A = Matrix.fromBlocks M₁ 0 0 M₂ := by
    rw [show b = (b₁.prod b₂).map e from rfl, LinearMap.toMatrix_map_left,
      LinearMap.toMatrix_map_right]
    have hmap : e.symm.toLinearMap.comp (A.comp e.toLinearMap) = A₁.prodMap A₂ := by
      rw [he, ← LinearMap.comp_assoc]
      apply LinearMap.ext
      intro x
      exact e.symm_apply_apply _
    rw [hmap, LinearMap.toMatrix_prodMap]
  have hMatrixEntry (i j : Fin (B.size (0 : Fin 2)) ⊕ Fin (B.size (1 : Fin 2))) :
      LinearMap.toMatrix c c A (ρ i) (ρ j) = Matrix.fromBlocks M₁ 0 0 M₂ i j := by
    rw [← hMatrix]
    simp only [c, LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply,
      Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  have hG : (g⁻¹ * γ * g).val = LinearMap.toMatrix c c A := by
    change c.toMatrix c₀ * γ.val * c₀.toMatrix c = _
    rw [show γ.val = LinearMap.toMatrix c₀ c₀ A from (LinearMap.toMatrix'_toLin' _).symm]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c c₀ c c₀ A
  refine ⟨g, m, ?_, ?_, ?_⟩
  · apply Units.ext
    change (g⁻¹ * γ * g).val = (B.leviEmbedding F m).val
    rw [hG]
    ext x y
    obtain ⟨i, rfl⟩ := ρ.surjective x
    obtain ⟨j, rfl⟩ := ρ.surjective y
    rw [hMatrixEntry]
    rcases i with a | a <;> rcases j with d | d
    · rw [hρ₁, hρ₁, Matrix.fromBlocks_apply₁₁]
      exact (B.leviEmbedding_apply_same F m (0 : Fin 2) a d).symm
    · rw [hρ₁, hρ₂, Matrix.fromBlocks_apply₁₂]
      exact (B.leviEmbedding_apply_ne F m _ _ (show (0 : Fin 2) ≠ 1 by decide)).symm
    · rw [hρ₂, hρ₁, Matrix.fromBlocks_apply₂₁]
      exact (B.leviEmbedding_apply_ne F m _ _ (show (1 : Fin 2) ≠ 0 by decide)).symm
    · rw [hρ₂, hρ₂, Matrix.fromBlocks_apply₂₂]
      exact (B.leviEmbedding_apply_same F m (1 : Fin 2) a d).symm
  · rw [hm₁]
    exact hc₁
  · rw [hm₂]
    exact hc₂

/-- Every positive-rank nonelliptic regular semisimple element is conjugate to a proper
standard two-block Levi, with a regular elliptic first block and regular semisimple second
block having a coprime characteristic polynomial. -/
theorem exists_twoBlock_of_regularSemisimple_of_not_regularElliptic
    {F : Type u} [Field F] {n : ℕ} (hn : 0 < n) (γ : GeneralLinear n F)
    (hreg : IsRegularSemisimple γ) (hell : ¬ IsRegularElliptic γ) :
    ∃ (k : ℕ) (hk : 0 < k) (hkn : k < n),
      let B := twoBlock n k hk hkn
      ∃ (g : GeneralLinear n F) (m : B.Levi F),
        g⁻¹ * γ * g = B.leviEmbedding F m ∧
        IsRegularElliptic (m (0 : Fin 2)) ∧ IsRegularSemisimple (m (1 : Fin 2)) ∧
        Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly := by
  have hnu : ¬ IsUnit γ.val.charpoly := by
    intro hu
    have hd := congrArg natDegree (γ.val.charpoly_monic.eq_one_of_isUnit hu)
    simpa using (Nat.ne_of_gt hn) (by simpa using hd)
  obtain ⟨p, hp, hpi, q, hfac⟩ := exists_monic_irreducible_factor γ.val.charpoly hnu
  have hq : q.Monic := hp.of_mul_monic_left (hfac ▸ γ.val.charpoly_monic)
  have hqnu : ¬ IsUnit q := by
    intro hu
    rw [hq.eq_one_of_isUnit hu, mul_one] at hfac
    exact hell ⟨hreg, hfac.symm ▸ hpi⟩
  have hk := hp.natDegree_pos_of_not_isUnit hpi.not_isUnit
  have hqk := hq.natDegree_pos_of_not_isUnit hqnu
  have hs : (p * q).Separable := hfac ▸ hreg
  have hsum : p.natDegree + q.natDegree = n := by
    rw [← hp.natDegree_mul hq, ← hfac, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hkn : p.natDegree < n := by omega
  obtain ⟨g, m, hg, hm₀, hm₁⟩ := exists_twoBlock_of_charpoly_mul γ hreg hp hq hfac hk hkn
  refine ⟨p.natDegree, hk, hkn, g, m, hg, ⟨?_, ?_⟩, ?_, ?_⟩
  · change (m (0 : Fin 2)).val.charpoly.Separable
    rw [hm₀]
    exact hs.of_mul_left
  · rw [hm₀]
    exact hpi
  · change (m (1 : Fin 2)).val.charpoly.Separable
    rw [hm₁]
    exact hs.of_mul_right
  · intro i j hij
    change Fin 2 at i j
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change IsCoprime (m (0 : Fin 2)).val.charpoly (m (1 : Fin 2)).val.charpoly
      rw [hm₀, hm₁]
      exact hs.isCoprime
    · change IsCoprime (m (1 : Fin 2)).val.charpoly (m (0 : Fin 2)).val.charpoly
      rw [hm₁, hm₀]
      exact hs.isCoprime.symm
    · exact (hij rfl).elim

end Langlands.BaseChange
