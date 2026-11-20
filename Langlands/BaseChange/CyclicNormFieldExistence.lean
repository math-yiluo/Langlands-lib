import Langlands.BaseChange.Norm
import Langlands.LinearAlgebra.MatrixAEvalConjugacyProof
import Langlands.LinearAlgebra.PolynomialInvariantFactors
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Block

/-! # Descent of the norm representative for field extensions -/

namespace Langlands.BaseChange

open _root_.Polynomial
open PolynomialInvariantFactors (Model Ordered existsModel eq_of_equiv)

universe u v w

noncomputable section

variable {K : Type u} [Field K] {L : Type v} [Field L]

section Companion

variable {ι : Type w} [DecidableEq ι]

private def companionBlocks (d : ι → ℕ) (q : ι → K[X]) :
    Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) K :=
  Matrix.blockDiagonal' fun i =>
    Matrix.of fun (a b : Fin (d i)) => ((X ^ (b.val + 1)) %ₘ q i).coeff a.val

private def companionMatrix {n : ℕ} (d : ι → ℕ) (q : ι → K[X])
    (e : (Σ i, Fin (d i)) ≃ Fin n) : Matrix (Fin n) (Fin n) K :=
  (companionBlocks d q).submatrix e.symm e.symm

private theorem companionMatrix_map {n : ℕ} (d : ι → ℕ) (q : ι → K[X])
    (e : (Σ i, Fin (d i)) ≃ Fin n) (hq : ∀ i, (q i).Monic) (f : K →+* L) :
    (companionMatrix d q e).map f = companionMatrix d (fun i => (q i).map f) e := by
  have h : (companionBlocks d q).map f = companionBlocks d (fun i => (q i).map f) := by
    rw [companionBlocks, Matrix.blockDiagonal'_map _ _ (map_zero f), companionBlocks]
    congr 1
    funext i
    ext a b
    change f (((X ^ (b.val + 1)) %ₘ q i).coeff a.val) =
      ((X ^ (b.val + 1)) %ₘ (q i).map f).coeff a.val
    rw [← coeff_map, map_modByMonic f (hq i), Polynomial.map_pow, map_X]
  exact congrArg (fun M : Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) L =>
    M.submatrix e.symm e.symm) h

private def quotientBasis (q : K[X]) (hq : q.Monic) {d : ℕ} (hd : q.natDegree = d) :
    Module.Basis (Fin d) K (PolynomialInvariantFactors.Quot q) :=
  (AdjoinRoot.powerBasisAux' hq).reindex (finCongr hd)

private theorem quotientBasis_repr_X_smul (q : K[X]) (hq : q.Monic) {d : ℕ}
    (hd : q.natDegree = d) (a b : Fin d) :
    (quotientBasis q hq hd).repr ((X : K[X]) • quotientBasis q hq hd b) a =
      ((X ^ (b.val + 1)) %ₘ q).coeff a.val := by
  subst d
  let bq := (AdjoinRoot.powerBasisAux' hq).reindex (Equiv.refl (Fin q.natDegree))
  change bq.repr (AdjoinRoot.mk q X * bq b) a = _
  have hb : AdjoinRoot.powerBasisAux' hq b = AdjoinRoot.mk q (X ^ b.val) := by
    calc
      _ = AdjoinRoot.root q ^ b.val := (AdjoinRoot.powerBasis' hq).basis_eq_pow b
      _ = _ := by rw [(AdjoinRoot.mk q).map_pow, AdjoinRoot.mk_X]
  simp only [bq, Module.Basis.reindex_refl]
  rw [hb]
  change (AdjoinRoot.powerBasisAux' hq).repr
    (AdjoinRoot.mk q X * AdjoinRoot.mk q (X ^ b.val)) a = _
  rw [← map_mul, ← pow_succ', AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk]

variable [Fintype ι]

private def companionBasis (d : ι → ℕ) (q : ι → K[X])
    (hq : ∀ i, (q i).Monic) (hd : ∀ i, (q i).natDegree = d i) :
    Module.Basis (Σ i, Fin (d i)) K (∀ i, PolynomialInvariantFactors.Quot (q i)) :=
  Pi.basis fun i => quotientBasis (q i) (hq i) (hd i)

private def companionAEval {n : ℕ} (d : ι → ℕ) (q : ι → K[X])
    (e : (Σ i, Fin (d i)) ≃ Fin n) (hq : ∀ i, (q i).Monic)
    (hd : ∀ i, (q i).natDegree = d i) :
    Module.AEval' (companionMatrix d q e).mulVecLin ≃ₗ[K[X]]
      (∀ i, PolynomialInvariantFactors.Quot (q i)) := by
  let b := (companionBasis d q hq hd).reindex e
  let T : Module.End K (∀ i, PolynomialInvariantFactors.Quot (q i)) :=
    Algebra.lsmul K K _ (X : K[X])
  have hT : LinearMap.toMatrix b b T = companionMatrix d q e := by
    ext a c
    rw [LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
    change _ = companionBlocks d q (e.symm a) (e.symm c)
    rcases e.symm a with ⟨i, s⟩
    rcases e.symm c with ⟨j, t⟩
    simp only [T, companionBasis, Pi.basis_repr, Pi.basis_apply, Algebra.lsmul_apply,
      Pi.smul_apply, companionBlocks]
    by_cases hij : i = j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq, Pi.single_eq_same]
      exact quotientBasis_repr_X_smul _ _ _ _ _
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hij, Pi.single_eq_of_ne hij,
        smul_zero, map_zero, Finsupp.zero_apply]
  refine LinearEquiv.ofAEval _ b.equivFun.symm fun x => ?_
  apply b.equivFun.injective
  rw [b.equivFun.apply_symm_apply]
  change (companionMatrix d q e).mulVec x = b.equivFun (T (b.equivFun.symm x))
  rw [← hT]
  have hrepr : (⇑(b.repr (b.equivFun.symm x)) : Fin n → K) = x :=
    b.equivFun.apply_symm_apply x
  change _ = ⇑(b.repr (T (b.equivFun.symm x)))
  simpa only [hrepr] using
    LinearMap.toMatrix_mulVec_repr b b T (b.equivFun.symm x)

end Companion

private def aevalEquivOfConj {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (g : GeneralLinear n K)
    (h : (g : Matrix (Fin n) (Fin n) K) * A *
      ((g⁻¹ : GeneralLinear n K) : Matrix (Fin n) (Fin n) K) = B) :
    Module.AEval' A.mulVecLin ≃ₗ[K[X]] Module.AEval' B.mulVecLin := by
  have hg : (g : Matrix (Fin n) (Fin n) K) * A = B * (g : Matrix (Fin n) (Fin n) K) := by
    rw [← h, mul_assoc, g.inv_mul, mul_one]
  let f := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  refine LinearEquiv.ofAEval _ (f.trans (Module.AEval'.of B.mulVecLin)) fun x => ?_
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, Module.AEval'.X_smul_of]
  apply (Module.AEval'.of B.mulVecLin).injective
  change (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) (Matrix.toLin' A x) =
    Matrix.toLin' B (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) x)
  rw [← Matrix.toLin'_mul_apply, ← Matrix.toLin'_mul_apply, hg]

private theorem modelMonic {qs : List K[X]} (hqs : Ordered qs) (i : Fin qs.length) :
    (qs.get i).Monic :=
  (hqs.2 _ (List.get_mem qs i)).1

private theorem existsCompanionForm {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    ∃ qs : List K[X], Ordered qs ∧
      ∃ e : (Σ i : Fin qs.length, Fin (qs.get i).natDegree) ≃ Fin n,
        ∃ g : GeneralLinear n K,
          g.val * A * (g⁻¹).val = companionMatrix (fun i => (qs.get i).natDegree) qs.get e := by
  have hc : aeval A.mulVecLin A.charpoly = 0 := by
    rw [← Matrix.charpoly_mulVecLin]
    exact LinearMap.aeval_self_charpoly _
  have hkill (x : Module.AEval' A.mulVecLin) : A.charpoly • x = 0 := by
    apply (Module.AEval'.of A.mulVecLin).symm.injective
    rw [Module.AEval.of_symm_smul, hc, zero_smul, map_zero]
  obtain ⟨qs, hqs, ⟨a⟩⟩ := existsModel A.charpoly_monic.ne_zero hkill
  let d (i : Fin qs.length) := (qs.get i).natDegree
  let b := companionBasis d qs.get (modelMonic hqs) (fun _ => rfl)
  have hcard : Fintype.card (Σ i, Fin (d i)) = n := calc
    _ = Module.finrank K (Model qs) := (Module.finrank_eq_card_basis b).symm
    _ = Module.finrank K (Module.AEval' A.mulVecLin) := (a.restrictScalars K).finrank_eq.symm
    _ = Module.finrank K (Fin n → K) := (Module.AEval'.of A.mulVecLin).finrank_eq.symm
    _ = n := Module.finrank_fin_fun K
  let e := Fintype.equivFinOfCardEq hcard
  let b' := companionAEval d qs.get e (modelMonic hqs) (fun _ => rfl)
  exact ⟨qs, hqs, e, matrixAEvalConjugacy K n A _ (a.trans b'.symm)⟩

private def quotientCongr {p q : K[X]} (h : p = q) :
    PolynomialInvariantFactors.Quot p ≃ₗ[K[X]] PolynomialInvariantFactors.Quot q := by
  subst q
  exact LinearEquiv.refl _ _

private def modelOfFn {m : ℕ} (q : Fin m → K[X]) :
    (∀ i, PolynomialInvariantFactors.Quot (q i)) ≃ₗ[K[X]] Model (List.ofFn q) := by
  let e : Fin (List.ofFn q).length ≃ Fin m := finCongr List.length_ofFn
  exact (LinearEquiv.piCongrLeft K[X] (fun i => PolynomialInvariantFactors.Quot (q i)) e).symm.trans
    (LinearEquiv.piCongrRight fun i => quotientCongr (List.get_ofFn q i).symm)

private def companionAEvalMap {n : ℕ} (qs : List K[X]) (hqs : Ordered qs)
    (e : (Σ i : Fin qs.length, Fin (qs.get i).natDegree) ≃ Fin n) (f : K →+* L) :
    Module.AEval' ((companionMatrix (fun i => (qs.get i).natDegree) qs.get e).map f).mulVecLin
      ≃ₗ[L[X]] Model (qs.map (Polynomial.map f)) := by
  let q (i : Fin qs.length) := (qs.get i).map f
  have hq : List.ofFn q = qs.map (Polynomial.map f) := by
    rw [show q = Polynomial.map f ∘ qs.get from rfl, ← List.map_ofFn, List.ofFn_get]
  rw [companionMatrix_map _ _ _ (modelMonic hqs), ← hq]
  exact (companionAEval _ q e (fun i => (modelMonic hqs i).map f)
    (fun _ => Polynomial.natDegree_map f)).trans (modelOfFn q)

private theorem orderedMap {qs : List K[X]} (hqs : Ordered qs) (f : K →+* L) :
    Ordered (qs.map (Polynomial.map f)) := by
  refine ⟨List.pairwise_map.mpr (hqs.1.imp (fun hpq => Polynomial.map_dvd f hpq)), ?_⟩
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  obtain ⟨hm, hd⟩ := hqs.2 p hp
  exact ⟨hm.map f, by rwa [Polynomial.natDegree_map]⟩

private theorem existsPolynomialLift {F : Type u} [Field F] {E : Type v} [Field E]
    [Algebra F E] {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : IsCyclicAlgebra σ l)
    {p : E[X]} (hp : p.map (σ : E →+* E) = p) :
    ∃ q : F[X], q.map (algebraMap F E) = p := by
  apply (Polynomial.mem_map_range (algebraMap F E)).mpr
  intro k
  apply hσ.2.2.2.2
  change (σ : E →+* E) (p.coeff k) = p.coeff k
  simpa only [coeff_map] using congrArg (fun r : E[X] => r.coeff k) hp

/-- Over a cyclic field extension, every norm product is associated with a base-field matrix. -/
theorem cyclicNormAssociated_of_field {F : Type u} [Field F] {E : Type v} [Field E]
    [Algebra F E] {σ : E ≃ₐ[F] E} {l n : ℕ} (hσ : IsCyclicAlgebra σ l)
    (δ : GeneralLinear n E) :
    ∃ γ : GeneralLinear n F, IsNormAssociated σ l δ γ := by
  let A := cyclicNorm σ l δ
  obtain ⟨qs, hqs, e, g, hg⟩ := existsCompanionForm A.val
  let d (i : Fin qs.length) := (qs.get i).natDegree
  let C := companionMatrix d qs.get e
  let f : E →+* E := σ
  have hσA : entrywiseAut σ n A = δ⁻¹ * A * δ := by
    change entrywiseAut σ n (cyclicNorm σ l δ) = δ⁻¹ * cyclicNorm σ l δ * δ
    rw [entrywiseAut_cyclicNorm, hσ.pow_eq_one, entrywiseAut_one_apply]
  have hσg : (entrywiseAut σ n g).val * (entrywiseAut σ n A).val *
      ((entrywiseAut σ n g)⁻¹).val = C.map f := by
    rw [← map_inv]
    change g.val.map f * A.val.map f * (g⁻¹).val.map f = C.map f
    simpa only [Matrix.map_mul] using congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map f) hg
  let a := (aevalEquivOfConj g hg).trans
    (companionAEval d qs.get e (modelMonic hqs) (fun _ => rfl))
  let aσ := (aevalEquivOfConj (entrywiseAut σ n g) hσg).trans (companionAEvalMap qs hqs e f)
  have hA : Module.AEval' A.val.mulVecLin ≃ₗ[E[X]]
      Module.AEval' (entrywiseAut σ n A).val.mulVecLin :=
    aevalEquivOfConj δ⁻¹ (by simpa only [inv_inv, Units.val_mul] using congrArg Units.val hσA.symm)
  have hfixed : qs = qs.map (Polynomial.map f) :=
    eq_of_equiv hqs (orderedMap hqs f) (a.symm.trans (hA.trans aσ))
  have hq (i : Fin qs.length) : (qs.get i).map f = qs.get i := by
    simpa only [List.get_eq_getElem, List.getElem_map] using
      (List.ext_get_iff.mp hfixed.symm).2 i.val (by simp [i.isLt]) i.isLt
  choose r hr using fun i => existsPolynomialLift hσ (hq i)
  let D := companionMatrix d r e
  have hrMonic (i : Fin qs.length) : (r i).Monic :=
    Polynomial.monic_map_iff.mp ((hr i).symm ▸ modelMonic hqs i)
  have hD : D.map (algebraMap F E) = C := by
    change (companionMatrix d r e).map (algebraMap F E) = C
    rw [companionMatrix_map _ _ _ hrMonic, funext hr]
  have hdet : D.det ≠ 0 := by
    intro hzero
    have hC : C.det ≠ 0 := by
      change (companionMatrix d qs.get e).det ≠ 0
      rw [← hg]
      exact Matrix.GeneralLinearGroup.det_ne_zero (g * A * g⁻¹)
    apply hC
    rw [← hD]
    change (RingHom.mapMatrix (algebraMap F E) D).det = 0
    rw [← RingHom.map_det, hzero, map_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero D hdet, g⁻¹, ?_⟩
  rw [inv_inv]
  exact Units.ext (hg.trans hD.symm)

end

end Langlands.BaseChange
