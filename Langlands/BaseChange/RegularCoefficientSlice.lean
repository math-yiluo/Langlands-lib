import Langlands.BaseChange.RegularCyclicBasis
import Langlands.BaseChange.RegularMatrixSlice
import Langlands.BaseChange.RegularOrbitParameters
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.UniformSpace.Matrix

noncomputable section

open Matrix Polynomial Set Topology
open scoped Matrix.Norms.Operator RightActions Ring

namespace Langlands.BaseChange

open Langlands.JacquetLanglands
open SigmaLiftCharacterIdentity (coefficients)

private theorem charpoly_charpolyActionMatrix {F : Type*} [Field F] {n : ℕ}
    (p : F[X]) (hp : p.Monic) (hn : p.natDegree = n) :
    (charpolyActionMatrix n p).charpoly = p := by
  subst n
  have he : Algebra.leftMulMatrix (AdjoinRoot.powerBasisAux' hp) (AdjoinRoot.root p) =
      charpolyActionMatrix p.natDegree p := by
    ext i j
    have hj : AdjoinRoot.powerBasisAux' hp j = AdjoinRoot.root p ^ j.val :=
      (AdjoinRoot.powerBasis' hp).basis_eq_pow j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hj, ← pow_succ', ← AdjoinRoot.mk_X,
      ← (AdjoinRoot.mk p).map_pow,
      AdjoinRoot.powerBasisAux'_repr_apply_to_fun, AdjoinRoot.modByMonicHom_mk]
    rfl
  rw [← he]
  exact (charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hp)).trans
    (AdjoinRoot.minpoly_powerBasis_gen_of_monic hp)

private theorem continuous_charpolyActionMatrix {F : Type*} [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] (n : ℕ) :
    Continuous fun b : Fin n → F => charpolyActionMatrix n (polynomialOfCoefficients b) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases hj : (j : ℕ) + 1 = n
  · have he (b : Fin n → F) : charpolyActionMatrix n (polynomialOfCoefficients b) i j = -b i := by
      let q := polynomialOfCoefficients b
      let r := ∑ k : Fin n, C (b k) * X ^ (k : ℕ)
      have hq := polynomialOfCoefficients_isMonicOfDegree b
      have hdeg : q.degree = n := (degree_eq_natDegree hq.monic.ne_zero).trans
        (congrArg (fun k : ℕ => (k : WithBot ℕ)) hq.natDegree_eq)
      have hr : r %ₘ q = r := (modByMonic_eq_self_iff hq.monic).mpr
        (hdeg ▸ degree_sum_fin_lt b)
      have heq : (X : F[X]) ^ n = q - r := by simp [q, r, polynomialOfCoefficients]
      change ((X ^ ((j : ℕ) + 1)) %ₘ q).coeff i = -b i
      rw [hj, heq, sub_modByMonic, modByMonic_self hq.monic, hr, zero_sub, coeff_neg]
      simp [r, finsetSum_coeff, Fin.val_eq_val]
    simp only [he]
    exact (continuous_apply i).neg
  · have he (b : Fin n → F) : charpolyActionMatrix n (polynomialOfCoefficients b) i j =
        ((X : F[X]) ^ ((j : ℕ) + 1)).coeff i := by
      let q := polynomialOfCoefficients b
      have hq := polynomialOfCoefficients_isMonicOfDegree b
      have hdeg : q.degree = n := (degree_eq_natDegree hq.monic.ne_zero).trans
        (congrArg (fun k : ℕ => (k : WithBot ℕ)) hq.natDegree_eq)
      change ((X ^ ((j : ℕ) + 1)) %ₘ q).coeff i = _
      rw [(modByMonic_eq_self_iff hq.monic).mpr]
      rw [degree_X_pow, hdeg, Nat.cast_lt]
      have := j.isLt
      omega
    simp only [he]
    exact continuous_const

/-- Nearby coefficients are realized by a continuous family of matrices passing through `γ`. -/
private theorem exists_companion_family {F : Type*} [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] {n : ℕ} (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ) :
    ∃ Y : (Fin n → F) → Matrix (Fin n) (Fin n) F,
      Continuous Y ∧ Y (coefficients γ) = γ.val ∧
        ∀ b, (Y b).charpoly = polynomialOfCoefficients b := by
  obtain ⟨v, hv⟩ := regularCyclicBasis F n γ.val hγ
  let g := hv.unit
  let Y := fun b : Fin n → F => g.val * charpolyActionMatrix n (polynomialOfCoefficients b) *
    (g⁻¹).val
  refine ⟨Y, (continuous_const.mul (continuous_charpolyActionMatrix n)).mul continuous_const,
    ?_, ?_⟩
  · have he : γ.val * g.val = g.val * charpolyActionMatrix n γ.val.charpoly := by
      rw [IsUnit.unit_spec]
      exact mul_cyclicBasisMatrix γ.val v
    have hg : g.val * (g⁻¹).val = 1 := congrArg Units.val (mul_inv_cancel g)
    dsimp only [Y]
    rw [polynomialOfCoefficients_coefficients, ← he, mul_assoc, hg, mul_one]
  · intro b
    have hq := polynomialOfCoefficients_isMonicOfDegree b
    dsimp only [Y]
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj,
      charpoly_charpolyActionMatrix _ hq.monic hq.natDegree_eq]

private theorem hasStrictFDerivAt_pow_one {F R : Type*} [NontriviallyNormedField F]
    [NormedRing R] [NormedAlgebra F R] (l : ℕ) :
    HasStrictFDerivAt (fun r : R => r ^ l)
      ((l : F) • ContinuousLinearMap.id F R) 1 := by
  have h := hasStrictFDerivAt_pow' (𝕜 := F) (𝔸 := R) l (x := 1)
  simp only [one_pow, one_smul, Finset.sum_const, Finset.card_range] at h
  convert h using 1
  ext x
  simp [Nat.cast_smul_eq_nsmul]

private theorem hasStrictFDerivAt_conj_mul_pow {F R P : Type*} [NontriviallyNormedField F]
    [NormedRing R] [NormedAlgebra F R] [HasSummableGeomSeries R]
    [NormedAddCommGroup P] [NormedSpace F P] (A : R) (l : ℕ)
    (G C : P →L[F] R) (x₀ : P) (hG₀ : G x₀ = 1) (hS₀ : 1 + C x₀ = 1) :
    HasStrictFDerivAt (fun x => G x * A * (1 + C x) ^ l * Ring.inverse (G x))
      ((G <• A) - A • G + A • ((l : F) • C)) x₀ := by
  have hpow : HasStrictFDerivAt (fun x => (1 + C x) ^ l) ((l : F) • C) x₀ := by
    have houter : HasStrictFDerivAt (fun r : R => r ^ l)
        ((l : F) • ContinuousLinearMap.id F R) (1 + C x₀) := by
      rw [hS₀]
      exact hasStrictFDerivAt_pow_one l
    simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp] using
      houter.comp x₀ (C.hasStrictFDerivAt.const_add (c := (1 : R)))
  have hinv : HasStrictFDerivAt (fun x => Ring.inverse (G x)) (-G) x₀ := by
    have houter : HasStrictFDerivAt (Ring.inverse : R → R) (-ContinuousLinearMap.id F R)
        (G x₀) := by
      rw [hG₀]
      convert hasStrictFDerivAt_ringInverse (𝕜 := F) (1 : Rˣ) using 1
      apply ContinuousLinearMap.ext
      intro r
      simp [ContinuousLinearMap.mulLeftRight_apply]
    simpa only [ContinuousLinearMap.neg_comp, ContinuousLinearMap.id_comp] using
      houter.comp x₀ G.hasStrictFDerivAt
  convert ((G.hasStrictFDerivAt.mul_const' A).mul' hpow).mul' hinv using 1
  apply ContinuousLinearMap.ext
  intro x
  simp only [Pi.mul_apply, hG₀, hS₀, one_mul, one_pow, Ring.inverse_one, _root_.smul_apply,
    _root_.add_apply, _root_.sub_apply, _root_.neg_apply, smul_eq_mul, op_smul_eq_mul, mul_one]
  noncomm_ring

/-! The derivative calculation above is the one used for norm neighbourhoods.
The inverse chart supplies a continuous choice of perturbation. -/

universe u

/-- A continuous polynomial perturbation of the identity with prescribed
coefficients for its power times the given regular element. -/
def RegularCoefficientSliceStatement : Prop :=
  ∀ (F : Type u) [NontriviallyNormedField F] [CompleteSpace F] [CharZero F]
    (n l : ℕ) (γ : GeneralLinear n F), 0 < l → IsRegularSemisimple γ →
    ∃ (V : Set (Fin n → F)) (hγV : coefficients γ ∈ V) (t : V → GeneralLinear n F),
      IsOpen V ∧ Continuous t ∧ t ⟨coefficients γ, hγV⟩ = 1 ∧
      (∀ b : V, ∃ c : Fin n → F, (t b).val = 1 + ∑ i : Fin n, c i • γ.val ^ (i : ℕ)) ∧
      ∀ b : V, coefficients (γ * t b ^ l) = b.val

theorem regularCoefficientSlice : RegularCoefficientSliceStatement.{u} := by
  intro F _ _ _ n l γ hl hγ
  obtain ⟨Y, hY, hYγ, hYchar⟩ := exists_companion_family γ hγ
  let M := Matrix (Fin n) (Fin n) F
  let P := M × (Fin n → F)
  let : @CompleteSpace M
      (inferInstance : NormedAddCommGroup M).toMetricSpace.toPseudoMetricSpace.toUniformSpace :=
    FiniteDimensional.complete F M
  let : @CompleteSpace P
      (inferInstance : NormedAddCommGroup P).toMetricSpace.toPseudoMetricSpace.toUniformSpace :=
    FiniteDimensional.complete F P
  let : HasSummableGeomSeries M := inferInstance
  let A : M := γ.val
  let x₀ : P := (1, 0)
  let L : (Fin n → F) →L[F] M :=
    ∑ i : Fin n, (ContinuousLinearMap.proj i).smulRight (A ^ (i : ℕ))
  have hL (c : Fin n → F) : L c = ∑ i : Fin n, c i • A ^ (i : ℕ) := by
    simp [L]
  let G : P →L[F] M := ContinuousLinearMap.fst F M (Fin n → F)
  let C₀ : P →L[F] M := L.comp (ContinuousLinearMap.snd F M (Fin n → F))
  have hG₀ : G x₀ = 1 := rfl
  have hS₀ : 1 + C₀ x₀ = 1 := by
    change (1 : M) + L 0 = 1
    simp
  let f : P → M := fun x => G x * A * (1 + C₀ x) ^ l * Ring.inverse (G x)
  let D : P →L[F] M := (G <• A) - A • G + A • ((l : F) • C₀)
  have hD (x : P) :
      D x = x.1 * A - A * x.1 + A * ((l : F) • ∑ i : Fin n, x.2 i • A ^ (i : ℕ)) := by
    change x.1 * A - A * x.1 + A * ((l : F) • L x.2) = _
    rw [hL]
  have hf : HasStrictFDerivAt f D x₀ := hasStrictFDerivAt_conj_mul_pow A l G C₀ x₀ hG₀ hS₀
  have hsurj : D.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro B
    obtain ⟨Z, c, hZ⟩ := exists_commutator_add_powers A hγ ((γ⁻¹ : GeneralLinear n F).val * B)
    refine ⟨(A * Z, fun i => (l : F)⁻¹ • c i), ?_⟩
    have hl' : (l : F) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
    have hcoeff :
        (l : F) • (∑ i : Fin n, ((l : F)⁻¹ • c i) • A ^ (i : ℕ)) =
          ∑ i : Fin n, c i • A ^ (i : ℕ) := by
      rw [Finset.smul_sum]
      simp [smul_smul, hl']
    have hAinv : A * (γ⁻¹ : GeneralLinear n F).val = 1 :=
      congrArg Units.val (mul_inv_cancel γ)
    change D (A * Z, fun i => (l : F)⁻¹ • c i) = B
    rw [hD, hcoeff, mul_assoc A Z A, ← mul_sub, ← mul_add, hZ, ← mul_assoc, hAinv, one_mul]
  let e := hf.implicitToOpenPartialHomeomorph f D hsurj
  let z : (Fin n → F) → M × D.ker := fun b => (Y b, 0)
  let U := z ⁻¹' e.target
  have hU : IsOpen U := e.open_target.preimage (hY.prodMk continuous_const)
  let ψ := e.symm ∘ z
  have hψ : ContinuousOn ψ U :=
    e.continuousOn_symm.comp (hY.prodMk continuous_const).continuousOn fun _ hb => hb
  have hfx₀ : f x₀ = A := by simp [f, hG₀, hS₀, Ring.inverse_one]
  have hz : z (coefficients γ) = e x₀ := by
    change (Y (coefficients γ), (0 : D.ker)) = e x₀
    rw [hf.implicitToOpenPartialHomeomorph_self hsurj, hYγ, hfx₀]
  have hx₀ : x₀ ∈ e.source := hf.mem_implicitToOpenPartialHomeomorph_source hsurj
  have hψγ : ψ (coefficients γ) = x₀ := by
    change e.symm (z (coefficients γ)) = x₀
    rw [hz, e.left_inv hx₀]
  let W : Set P := {x | IsUnit (G x) ∧ IsUnit (1 + C₀ x)}
  have hW : IsOpen W := (Units.isOpen.preimage G.continuous).inter
    (Units.isOpen.preimage (continuous_const.add C₀.continuous))
  let V := U ∩ ψ ⁻¹' W
  have hγV : coefficients γ ∈ V := by
    refine ⟨?_, ?_⟩
    · change z (coefficients γ) ∈ e.target
      rw [hz]
      exact e.map_source hx₀
    · change IsUnit (G (ψ (coefficients γ))) ∧ IsUnit (1 + C₀ (ψ (coefficients γ)))
      simp only [hψγ, hG₀, hS₀, isUnit_one, and_self]
  let t : V → GeneralLinear n F := fun b => ((show ψ b.val ∈ W from b.property.2).2).unit
  have htval (b : V) : (t b).val = 1 + C₀ (ψ b.val) := IsUnit.unit_spec _
  refine ⟨V, hγV, t, hψ.isOpen_inter_preimage hU hW, ?_, ?_, ?_, ?_⟩
  · have hEmb : IsOpenEmbedding (Units.val : Mˣ → M) := Units.isOpenEmbedding_val
    apply hEmb.isEmbedding.continuous_iff.mpr
    change Continuous fun b : V => (t b).val
    simp only [htval]
    exact continuous_const.add (C₀.continuous.comp (hψ.mono inter_subset_left).domRestrict)
  · apply Units.ext
    rw [htval]
    change 1 + C₀ (ψ (coefficients γ)) = 1
    rw [hψγ, hS₀]
  · intro b
    exact ⟨(ψ b.val).2, (htval b).trans (congrArg (1 + ·) (hL (ψ b.val).2))⟩
  · intro b
    have he : f (ψ b.val) = Y b.val := by
      have hright := congrArg Prod.fst (e.right_inv (show z b.val ∈ e.target from b.property.1))
      simpa only [e, ψ, Function.comp_apply, z, hf.implicitToOpenPartialHomeomorph_fst] using hright
    have hg : IsUnit (G (ψ b.val)) := (show ψ b.val ∈ W from b.property.2).1
    let g := hg.unit
    have hmat : g.val * (γ * t b ^ l).val * (g⁻¹).val = Y b.val := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, htval, ← Ring.inverse_unit g, hg.unit_spec]
      rw [← mul_assoc]
      exact he
    have hchar : (γ * t b ^ l).val.charpoly = polynomialOfCoefficients b.val := by
      rw [← hYchar, ← hmat, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    funext i
    change (γ * t b ^ l).val.charpoly.coeff i = b.val i
    rw [hchar]
    simp [polynomialOfCoefficients, finsetSum_coeff, coeff_X_pow,
      Nat.ne_of_lt i.isLt, Fin.val_eq_val]

end Langlands.BaseChange
