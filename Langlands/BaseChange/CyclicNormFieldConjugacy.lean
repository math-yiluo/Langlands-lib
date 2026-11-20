import Langlands.BaseChange.CyclicNormFieldReduction
import Langlands.LinearAlgebra.FiniteModuleCancellation
import Mathlib.FieldTheory.Fixed
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Ordinary and twisted conjugacy over cyclic field extensions -/

namespace Langlands.BaseChange

open Matrix

universe u v w

noncomputable section

private def swapIndices (K : Type u) [Semiring K] {ι : Type v} {κ : Type w} :
    (ι → κ → K) ≃ₗ[K] (κ → ι → K) where
  toFun f j i := f i j
  invFun f i j := f j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def toVectorEquiv (K : Type u) [CommRing K] (n : ℕ) :
    GeneralLinear n K ≃* ((Fin n → K) ≃ₗ[K] Fin n → K) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K _)

private theorem toVectorEquiv_apply {K : Type u} [CommRing K] {n : ℕ}
    (g : GeneralLinear n K) (x : Fin n → K) : toVectorEquiv K n g x = g.val *ᵥ x := rfl

private theorem toVectorEquiv_mul_apply {K : Type u} [CommRing K] {n : ℕ}
    (g h : GeneralLinear n K) (x : Fin n → K) :
    toVectorEquiv K n (g * h) x = toVectorEquiv K n g (toVectorEquiv K n h x) := by
  rw [map_mul]
  rfl

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] {n : ℕ}

private def coefficientExpansion {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin n → E) ≃ₗ[F] (Fin d → Fin n → F) :=
  (LinearEquiv.piCongrRight (fun _ : Fin n => b.equivFun)).trans (swapIndices F)

private theorem coefficientExpansion_baseChange {d : ℕ} (b : Module.Basis (Fin d) F E)
    (a : GeneralLinear n F) (x : Fin n → E) (i : Fin d) :
    coefficientExpansion b (toVectorEquiv E n (baseChange F E n a) x) i =
      toVectorEquiv F n a (coefficientExpansion b x i) := by
  funext j
  change b.equivFun (∑ k : Fin n, algebraMap F E (a j k) * x k) i =
    ∑ k : Fin n, a j k * b.equivFun (x k) i
  calc
    _ = ∑ k : Fin n, b.equivFun (a j k • x k) i := by
      simp only [Algebra.smul_def, map_sum, Finset.sum_apply]
    _ = _ := by simp only [map_smul, Pi.smul_apply, smul_eq_mul]

/-- Conjugacy between two matrices over the base field is reflected by any finite field
extension. After expanding extension coefficients in a basis, it is an isomorphism of
positive copies of the base-field operators. -/
theorem baseChange_reflects_conjugacy_of_finite [Module.Finite F E] {a b : GeneralLinear n F}
    (g : GeneralLinear n E) (hg : (baseChange F E n a) * g = g * (baseChange F E n b)) :
    ∃ y : GeneralLinear n F, y⁻¹ * a * y = b := by
  let d := Module.finrank F E
  have hd : 0 < d := Module.finrank_pos
  let exp : (Fin n → E) ≃ₗ[F] (Fin d → Fin n → F) :=
    coefficientExpansion (Module.finBasis F E)
  let G := (toVectorEquiv E n g).restrictScalars F
  let e := exp.symm.trans (G.trans exp)
  have expand (a : GeneralLinear n F) (x : Fin n → E) (i : Fin d) :
      exp (toVectorEquiv E n (baseChange F E n a) x) i = toVectorEquiv F n a (exp x i) :=
    coefficientExpansion_baseChange _ a x i
  have hG (x : Fin n → E) :
      G (toVectorEquiv E n (baseChange F E n b) x) = toVectorEquiv E n (baseChange F E n a) (G x) := by
    change toVectorEquiv E n g (toVectorEquiv E n (baseChange F E n b) x) =
      toVectorEquiv E n (baseChange F E n a) (toVectorEquiv E n g x)
    rw [← toVectorEquiv_mul_apply, ← toVectorEquiv_mul_apply, hg]
  have hcop (x : Fin d → Fin n → F) :
      e (fun i => toVectorEquiv F n b (x i)) = fun i => toVectorEquiv F n a (e x i) := by
    have hx : (fun i => toVectorEquiv F n b (x i)) = exp (toVectorEquiv E n (baseChange F E n b) (exp.symm x)) := by
      funext i
      rw [expand, exp.apply_symm_apply]
    rw [hx]
    have he (z : Fin n → E) : e (exp z) = exp (G z) := by
      change exp (G (exp.symm (exp z))) = _
      rw [exp.symm_apply_apply]
    rw [he, hG]
    funext i
    exact expand a (G (exp.symm x)) i
  obtain ⟨e₀, he₀⟩ := FiniteModuleCancellation.exists_intertwiningEquiv_of_copies hd
    (fun _ : Unit => (toVectorEquiv F n b).toLinearMap)
    (fun _ : Unit => (toVectorEquiv F n a).toLinearMap) e (fun _ x i => congrFun (hcop x) i)
  let y := (toVectorEquiv F n).symm e₀
  have hy : toVectorEquiv F n y = e₀ := (toVectorEquiv F n).apply_symm_apply e₀
  have hy' : a * y = y * b := (toVectorEquiv F n).injective (by
    ext1 x
    rw [toVectorEquiv_mul_apply, toVectorEquiv_mul_apply, hy]
    exact (he₀ () x).symm)
  exact ⟨y, by rw [mul_assoc, hy', ← mul_assoc, inv_mul_cancel, one_mul]⟩

/-- Two base-field representatives of the same cyclic norm are conjugate over the base field. -/
theorem cyclicNormAssociated_unique_of_field {σ : E ≃ₐ[F] E} {l : ℕ}
    (h : IsCyclicAlgebra σ l) {δ : GeneralLinear n E} {a b : GeneralLinear n F}
    (ha : IsNormAssociated σ l δ a) (hb : IsNormAssociated σ l δ b) :
    ∃ y : GeneralLinear n F, y⁻¹ * a * y = b := by
  have : Module.Finite F E := h.1
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  apply baseChange_reflects_conjugacy_of_finite (x⁻¹ * y)
  rw [← hx, ← hy]
  group

private def twistLin (σ : E ≃ₐ[F] E) (δ : GeneralLinear n E) : Module.End F (Fin n → E) :=
  ((toVectorEquiv E n δ).toLinearMap.restrictScalars F).comp
    (LinearMap.pi fun j => σ.toAlgHom.toLinearMap.comp (LinearMap.proj j))

private theorem twistLin_apply (σ : E ≃ₐ[F] E) (δ : GeneralLinear n E) (x : Fin n → E) :
    twistLin σ δ x = toVectorEquiv E n δ (fun i => σ (x i)) := rfl

private theorem twistLin_smul (σ : E ≃ₐ[F] E) (δ : GeneralLinear n E) (a : E) (x : Fin n → E) :
    twistLin σ δ (a • x) = σ a • twistLin σ δ x := by
  change toVectorEquiv E n δ (fun i => σ (a * x i)) =
    σ a • toVectorEquiv E n δ (fun i => σ (x i))
  simp only [map_mul]
  exact (toVectorEquiv E n δ).map_smul (σ a) (fun i => σ (x i))

private theorem twistLin_toVectorEquiv (σ : E ≃ₐ[F] E) (δ g : GeneralLinear n E) (x : Fin n → E) :
    twistLin σ δ (toVectorEquiv E n g x) =
      toVectorEquiv E n (δ * entrywiseAut σ n g) (fun i => σ (x i)) := by
  rw [twistLin_apply, toVectorEquiv_mul_apply]
  apply congrArg (toVectorEquiv E n δ)
  funext i
  exact RingHom.map_mulVec σ.toRingHom g.val x i

private theorem cyclicIndex_step {α : Type*} {l : ℕ} {a : ℕ → α} (ha : a l = a 0) (i : Fin l) :
    a (finRotate l i).val = a (i.val + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  rw [coe_finRotate]
  split_ifs with hi
  · rw [hi, Fin.val_last, ha]
  · rfl

private theorem exists_galois_matrix {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l)
    (b : Module.Basis (Fin l) F E) :
    ∃ B : GeneralLinear l E, ∀ i j, B i j = (σ ^ i.val) (b j) := by
  let a (i : Fin l) : E →ₐ[F] E := (σ ^ i.val).toAlgHom
  have ha : Function.Injective a := by
    intro i j hij
    have he : σ ^ i.val = σ ^ j.val := AlgEquiv.ext (fun x => DFunLike.congr_fun hij x)
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := σ) _ _ he
    · simpa only [Set.mem_Iio, h.2.2.2.1] using i.isLt
    · simpa only [Set.mem_Iio, h.2.2.2.1] using j.isLt
  let Q : Matrix (Fin l) (Fin l) E := fun i j => (σ ^ i.val) (b j)
  let f : (E →ₗ[F] E) ≃ₗ[E] (Fin l → E) := (b.constr E).symm
  have hlin := (linearIndependent_toLinearMap F E E).comp a ha
  have hrows : LinearIndependent E Q.row :=
    hlin.map' f.toLinearMap (LinearMap.ker_eq_bot.2 f.injective)
  obtain ⟨B, hB⟩ := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ⟨B, fun i j => congrFun (congrFun hB i) j⟩

private def onCopies {l : ℕ} (B : GeneralLinear l E) :
    (Fin l → Fin n → E) ≃ₗ[E] (Fin l → Fin n → E) :=
  (swapIndices E).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin n => toVectorEquiv E l B)).trans (swapIndices E))

private theorem onCopies_apply {l : ℕ} (B : GeneralLinear l E) (x : Fin l → Fin n → E) (i : Fin l) :
    onCopies B x i = ∑ j : Fin l, B i j • x j := by
  funext k
  change ((B.val *ᵥ fun j => x j k) i) = (∑ j : Fin l, B i j • x j) k
  rw [Finset.sum_apply]
  rfl

private theorem cyclicNorm_succ_mul_first {σ : E ≃ₐ[F] E} (i : ℕ) (δ : GeneralLinear n E) :
    cyclicNorm σ (i + 1) δ = δ * entrywiseAut σ n (cyclicNorm σ i δ) := by
  rw [cyclicNorm_succ, entrywiseAut_cyclicNorm]
  group

/-- Over a cyclic field extension, conjugate norms give twisted-conjugate matrices.
The conjugates of a field basis turn the orbit of a norm conjugator into an
intertwining equivalence on copies of the underlying semilinear operators. -/
theorem twistedConj_of_cyclicNorm_conj_of_field {σ : E ≃ₐ[F] E} {l : ℕ}
    (h : IsCyclicAlgebra σ l) {δ δ' : GeneralLinear n E}
    (g : GeneralLinear n E) (hg : g⁻¹ * cyclicNorm σ l δ * g = cyclicNorm σ l δ') :
    ∃ x : GeneralLinear n E, x⁻¹ * δ * entrywiseAut σ n x = δ' := by
  have : Module.Finite F E := h.1
  let b := Module.finBasisOfFinrankEq F E h.2.1
  obtain ⟨B, hB⟩ := exists_galois_matrix h b
  have hBstep (i j : Fin l) : B (finRotate l i) j = σ (B i j) := by
    rw [hB, hB]
    have hperiod : (σ ^ l) (b j) = (σ ^ 0) (b j) := by rw [h.pow_eq_one, pow_zero]
    rw [cyclicIndex_step (a := fun k => (σ ^ k) (b j)) hperiod, pow_succ', AlgEquiv.mul_apply]
  let basisChange : (Fin l → Fin n → E) ≃ₗ[E] (Fin l → Fin n → E) := onCopies B
  have hShift (ζ : GeneralLinear n E) (x : Fin l → Fin n → E) (i : Fin l) :
      basisChange (fun j => twistLin σ ζ (x j)) (finRotate l i) =
        twistLin σ ζ (basisChange x i) := by
    change onCopies B (fun j => twistLin σ ζ (x j)) (finRotate l i) =
      twistLin σ ζ (onCopies B x i)
    simp only [onCopies_apply, hBstep, map_sum, twistLin_smul]
  let c (i : ℕ) : GeneralLinear n E :=
    cyclicNorm σ i δ * entrywiseAut (σ ^ i) n g * (cyclicNorm σ i δ')⁻¹
  have hcZero : c 0 = g := by simp [c, entrywiseAut_one_apply]
  have hcLast : c l = g := by
    have hn : cyclicNorm σ l δ * g = g * cyclicNorm σ l δ' := by rw [← hg]; group
    dsimp only [c]
    rw [h.pow_eq_one, entrywiseAut_one_apply, hn]
    group
  have hcSucc (i : ℕ) : c (i + 1) = δ * entrywiseAut σ n (c i) * δ'⁻¹ := by
    dsimp only [c]
    rw [cyclicNorm_succ_mul_first, cyclicNorm_succ_mul_first, pow_succ', entrywiseAut_mul_apply,
      map_mul, map_mul, map_inv]
    group
  have hcStep (i : Fin l) : c (finRotate l i).val = δ * entrywiseAut σ n (c i.val) * δ'⁻¹ := by
    rw [cyclicIndex_step (hcLast.trans hcZero.symm), hcSucc]
  have hDiag (i : Fin l) (x : Fin n → E) :
      twistLin σ δ (toVectorEquiv E n (c i.val) x) =
        toVectorEquiv E n (c (finRotate l i).val) (twistLin σ δ' x) := by
    have hm : δ * entrywiseAut σ n (c i.val) = c (finRotate l i).val * δ' := by
      rw [hcStep]
      group
    rw [twistLin_toVectorEquiv, twistLin_apply, ← toVectorEquiv_mul_apply, hm]
  let diag := LinearEquiv.piCongrRight (fun i : Fin l => toVectorEquiv E n (c i.val))
  let e := basisChange.trans (diag.trans basisChange.symm)
  have he (x : Fin l → Fin n → E) (i : Fin l) :
      basisChange (e x) i = toVectorEquiv E n (c i.val) (basisChange x i) := by
    change basisChange (basisChange.symm (diag (basisChange x))) i = _
    rw [basisChange.apply_symm_apply]
    rfl
  have hcopies (x : Fin l → Fin n → E) :
      e (fun j => twistLin σ δ' (x j)) = fun j => twistLin σ δ (e x j) := by
    apply basisChange.injective
    funext k
    obtain ⟨i, rfl⟩ := (finRotate l).surjective k
    rw [he, hShift, hShift, he, hDiag]
  let ops (ζ : GeneralLinear n E) (o : Option E) : Module.End F (Fin n → E) :=
    match o with
    | none => twistLin σ ζ
    | some a => a • LinearMap.id
  obtain ⟨f, hf⟩ := FiniteModuleCancellation.exists_intertwiningEquiv_of_copies h.pos (ops δ')
    (ops δ) (e.restrictScalars F) (by
      intro o x i
      cases o with
      | none => exact congrFun (hcopies x) i
      | some a => exact congrFun (e.map_smul a x) i)
  let fE : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
    { f.toAddEquiv with map_smul' := fun a x => hf (some a) x }
  let x := (toVectorEquiv E n).symm fE
  have hx : toVectorEquiv E n x = fE := (toVectorEquiv E n).apply_symm_apply fE
  have hm : δ * entrywiseAut σ n x = x * δ' := (toVectorEquiv E n).injective (by
    ext1 z
    let w : Fin n → E := fun i => σ.symm (z i)
    have hz : (fun i => σ (w i)) = z := funext fun i => σ.apply_symm_apply (z i)
    have hw := hf none w
    change fE (twistLin σ δ' w) = twistLin σ δ (fE w) at hw
    rw [← hx, twistLin_toVectorEquiv, twistLin_apply, ← toVectorEquiv_mul_apply, hz] at hw
    exact hw.symm)
  exact ⟨x, by rw [mul_assoc, hm, ← mul_assoc, inv_mul_cancel, one_mul]⟩

end

/-- Existence of a base-field representative for each cyclic norm over a field. -/
def FieldCyclicNormExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] (E : Type v) [Field E] [Algebra F E] (σ : E ≃ₐ[F] E)
    (l n : ℕ), IsCyclicAlgebra σ l →
      ∀ δ : GeneralLinear n E, ∃ γ : GeneralLinear n F, IsNormAssociated σ l δ γ

/-- Field existence suffices for the full norm lemma. -/
def CyclicNormLemmaExistenceReductionStatement : Prop :=
  FieldCyclicNormExistenceStatement.{u,v} → CyclicNormLemmaStatement.{u,v}

theorem cyclicNormLemma_of_field_exists : CyclicNormLemmaExistenceReductionStatement.{u,v} := by
  intro h
  apply cyclicNormLemma_of_field.{u,v}
  intro F _ E _ _ σ l n hσ
  refine ⟨h F E σ l n hσ, ?_, ?_⟩
  · intro δ a b ha hb
    exact cyclicNormAssociated_unique_of_field hσ ha hb
  · rintro δ δ' ⟨g, hg⟩
    exact twistedConj_of_cyclicNorm_conj_of_field hσ g hg

end Langlands.BaseChange
