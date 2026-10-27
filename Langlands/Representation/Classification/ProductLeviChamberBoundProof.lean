import Langlands.Representation.Classification.ProductLeviChamberBoundStatement
import Langlands.Representation.Classification.ProductLeviDualOppositeAdapter
import Langlands.Representation.Jacquet.RefinedUpperCompressionProof
import Langlands.Representation.CuspidalSupport.UniformBlockIwahoriBasis
import Langlands.Analysis.EndomorphismPowerBound
import Langlands.Group.GL.CartanQuotientLawsProof

/-!
# Chamber bound for matrix coefficients of a product Levi

Proof of `GLProductLeviChamberCoefficientBoundStatement`.
-/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.ProductLeviChamber

open GeneralLinear Geometric

universe uF uV

/-! ### Auxiliary block shapes -/

/-- The block shape of `N` with a single block. -/
def oneBlock (N : ℕ) (hN : 0 < N) : BlockShape N where
  length := 1
  size := fun _ => N
  positive := fun _ => hN
  sum_eq := by simp

/-- The block shape `(k, N - k)` of `N`. -/
def twoBlock (N k : ℕ) (hk : 0 < k) (hkN : k < N) : BlockShape N where
  length := 2
  size := ![k, N - k]
  positive := by
    intro i
    fin_cases i
    · exact hk
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      omega
  sum_eq := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    omega

theorem twoBlock_index_val (N k : ℕ) (hk : 0 < k) (hkN : k < N)
    (i : Fin (twoBlock N k hk hkN).length) (r : Fin ((twoBlock N k hk hkN).size i)) :
    ((twoBlock N k hk hkN).index i r : ℕ) = (if i.val = 0 then 0 else k) + r := by
  change ((finSigmaFinEquiv.trans (finCongr (twoBlock N k hk hkN).sum_eq)) ⟨i, r⟩ : ℕ) = _
  rw [Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  have hi : i.val < 2 := i.isLt
  rcases i with ⟨i, hi'⟩
  interval_cases i
  · simp
  · simp [twoBlock]

/-- The block containing a coordinate, as a natural number. -/
def blockLabel {N : ℕ} (B : BlockShape N) (x : Fin N) : ℕ :=
  (B.indexEquiv.symm x).1.val

theorem twoBlock_blockLabel (N k : ℕ) (hk : 0 < k) (hkN : k < N) (x : Fin N) :
    blockLabel (twoBlock N k hk hkN) x = if x.val < k then 0 else 1 := by
  obtain ⟨⟨i, r⟩, rfl⟩ := (twoBlock N k hk hkN).indexEquiv.surjective x
  unfold blockLabel
  rw [Equiv.symm_apply_apply]
  have h := twoBlock_index_val N k hk hkN i r
  change ((twoBlock N k hk hkN).indexEquiv ⟨i, r⟩ : ℕ) = _ at h
  have hr : (r : ℕ) < (twoBlock N k hk hkN).size i := r.isLt
  rcases i with ⟨i, hi⟩
  have hi2 : i < 2 := hi
  interval_cases i
  · simp only [twoBlock, Fin.zero_eta, Matrix.cons_val_zero] at hr
    simp only [ite_true] at h
    simp only [h]
    simp [hr]
  · simp only [Fin.mk_one, twoBlock, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hr
    simp only [one_ne_zero, ite_false] at h
    rw [h]
    simp

theorem oneBlock_blockLabel (N : ℕ) (hN : 0 < N) (x : Fin N) :
    blockLabel (oneBlock N hN) x = 0 := by
  unfold blockLabel
  have : ((oneBlock N hN).indexEquiv.symm x).1.val < 1 :=
    ((oneBlock N hN).indexEquiv.symm x).1.isLt
  omega

/-- A block scalar matrix is the diagonal matrix of the scalars of the blocks. -/
theorem blockScalar_val {N : ℕ} (B : BlockShape N) (R : Type*) [CommRing R]
    (c : Fin B.length → Rˣ) :
    (B.blockScalar R c).val = Matrix.diagonal (fun x => (c (B.indexEquiv.symm x).1 : R)) := by
  ext x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨i', r'⟩, rfl⟩ := B.indexEquiv.surjective y
  change B.blockScalar R c (B.index i r) (B.index i' r') = _
  by_cases h : i = i'
  · subst h
    rw [B.blockScalar_apply_same]
    by_cases hr : r = r'
    · subst hr
      rw [ite_eq_left_iff.mpr (fun h => absurd rfl h), Matrix.diagonal_apply_eq]
      rw [Equiv.symm_apply_apply]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hr), Matrix.diagonal_apply_ne]
      intro he
      exact hr ((B.index i).injective he)
  · rw [B.blockScalar_apply_ne R c r r' h, Matrix.diagonal_apply_ne]
    intro he
    exact h (congrArg Sigma.fst (B.indexEquiv.injective he))

/-! ### Fundamental coweights -/

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The integer tuple of the fundamental coweight `diag(ϖ I_k, I_(N-k))`. -/
def fund (N k : ℕ) : Fin N → ℤ := fun x => if x.val < k then 1 else 0

theorem fund_antitone (N k : ℕ) : Antitone (fund N k) := by
  intro x y hxy
  have : x.val ≤ y.val := hxy
  unfold fund
  split_ifs <;> omega

theorem degree_fund (N k : ℕ) (hkN : k ≤ N) :
    CartanQuotient.degree (fund N k) = ((k * (N - k) : ℕ) : ℤ) := by
  unfold CartanQuotient.degree fund
  have hterm : ∀ i j : Fin N,
      (if i < j then (if i.val < k then (1 : ℤ) else 0) - (if j.val < k then 1 else 0) else 0) =
        (if i.val < k then (1 : ℤ) else 0) * (if ¬ (j.val < k) then (1 : ℤ) else 0) := by
    intro i j
    have h : i < j ↔ i.val < j.val := Iff.rfl
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte]
      have : i.val < j.val := h.mp hij
      split_ifs <;> omega
    · simp only [hij, ↓reduceIte]
      have : ¬ i.val < j.val := fun h' => hij (h.mpr h')
      split_ifs <;> omega
  calc ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ((if i.val < k then (1 : ℤ) else 0) - (if j.val < k then 1 else 0))
      = ∑ i : Fin N, ∑ j : Fin N,
          (if i.val < k then (1 : ℤ) else 0) * (if ¬ (j.val < k) then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun j _ => hterm i j
    _ = (∑ i : Fin N, (if i.val < k then (1 : ℤ) else 0)) *
          ∑ j : Fin N, (if ¬ (j.val < k) then (1 : ℤ) else 0) := by
        rw [Finset.sum_mul_sum]
    _ = ((k * (N - k) : ℕ) : ℤ) := by
        rw [Finset.sum_boole, Finset.sum_boole]
        have h1 : (Finset.univ.filter (fun i : Fin N => i.val < k)).card = k := by
          rw [Fin.card_filter_val_lt]
          omega
        have h2 := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => i.val < k)
        rw [Finset.card_univ, Fintype.card_fin, h1] at h2
        rw [h1]
        push_cast
        have h3 : ((Finset.univ.filter (fun i : Fin N => ¬ i.val < k)).card : ℤ) =
            (N : ℤ) - k := by
          omega
        rw [h3]
        push_cast [hkN]
        ring

theorem delta_fund (N k : ℕ) (hkN : k ≤ N) :
    CartanQuotient.delta T (fund N k) =
      (T.residueCardinality : ℝ) ^ (-((k * (N - k) : ℕ) : ℤ)) := by
  rw [CartanQuotient.delta, degree_fund N k hkN]

/-- The uniformizer and one, in the two blocks. -/
def twoScalars {L : ℕ} : Fin L → F.Carrierˣ :=
  fun l => if l.val = 0 then LocalFactor.PadicAbelian.uniformizerUnit T else 1

theorem twoBlock_blockScalar (N k : ℕ) (hk : 0 < k) (hkN : k < N) (B : BlockShape N)
    (hB : B = twoBlock N k hk hkN) :
    B.blockScalar F.Carrier (twoScalars T) = CartanQuotient.representative T (fund N k) := by
  subst hB
  apply Units.ext
  rw [blockScalar_val, CartanQuotient.representative, Iwasawa.torus_val]
  congr 1
  funext x
  have hl := twoBlock_blockLabel N k hk hkN x
  unfold blockLabel at hl
  unfold twoScalars fund
  rw [hl]
  split_ifs <;> simp_all

theorem uniformizer_abs :
    T.normalizedAbs ((LocalFactor.PadicAbelian.uniformizerUnit T : F.Carrierˣ) : F.Carrier) =
      (T.residueCardinality : ℝ)⁻¹ := by
  have h := LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T 1
  rw [zpow_one, zpow_neg_one] at h
  exact h

theorem residueCardinality_gt_one_real : (1 : ℝ) < T.residueCardinality := by
  exact_mod_cast T.residueCardinality_gt_one

theorem twoBlock_isStrictlyContracting (N k : ℕ) (hk : 0 < k) (hkN : k < N) (B : BlockShape N)
    (hB : B = twoBlock N k hk hkN) : B.IsStrictlyContracting T (twoScalars T) := by
  subst hB
  intro i j hij
  have hi : i.val < 2 := i.isLt
  have hj : j.val < 2 := j.isLt
  have hij' : i.val < j.val := hij
  have hi0 : i.val = 0 := by omega
  have hj1 : j.val = 1 := by omega
  rw [BlockShape.blockScalarRatio_apply, T.normalizedAbsUnits_coe]
  simp only [twoScalars, hi0, hj1, ↓reduceIte, one_ne_zero, inv_one, mul_one]
  rw [uniformizer_abs]
  exact inv_lt_one_of_one_lt₀ (residueCardinality_gt_one_real T)

theorem isStrictlyContracting_of_length_eq_one {N : ℕ} (B : BlockShape N) (hB : B.length = 1)
    (c : Fin B.length → F.Carrierˣ) : B.IsStrictlyContracting T c := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val < j.val := hij
  omega

theorem leviModulus_of_length_eq_one {N : ℕ} (B : BlockShape N) (hB : B.length = 1)
    (g : B.Levi F.Carrier) : T.leviModulus B g = 1 := by
  rw [T.leviModulus_apply]
  apply Finset.prod_eq_one
  intro i _
  apply Finset.prod_eq_one
  intro j hj
  have hij : i < j := (Finset.mem_filter.mp hj).2
  have hi := i.isLt
  have hj' := j.isLt
  have hij' : i.val < j.val := hij
  omega

theorem twoBlock_leviModulus (N k : ℕ) (hk : 0 < k) (hkN : k < N) (B : BlockShape N)
    (hB : B = twoBlock N k hk hkN) :
    ((T.leviModulus B (B.blockScalarLevi F.Carrier (twoScalars T)) : ℝ≥0) : ℝ) =
      (T.residueCardinality : ℝ) ^ (-((k * (N - k) : ℕ) : ℤ)) := by
  subst hB
  rw [T.leviModulus_apply]
  let i0 : Fin (twoBlock N k hk hkN).length := ⟨0, show 0 < 2 by omega⟩
  let i1 : Fin (twoBlock N k hk hkN).length := ⟨1, show 1 < 2 by omega⟩
  have hlen : ∀ i : Fin (twoBlock N k hk hkN).length, i.val < 2 := fun i => i.isLt
  rw [Finset.prod_eq_single i0]
  · rw [Finset.prod_eq_single_of_mem i1]
    · simp only [BlockShape.blockScalarLevi_apply, T.determinantNorm_scalar]
      have hs0 : (twoBlock N k hk hkN).size i0 = k := rfl
      have hs1 : (twoBlock N k hk hkN).size i1 = N - k := rfl
      have hc0 : twoScalars T i0 = LocalFactor.PadicAbelian.uniformizerUnit T := by
        simp [twoScalars, i0]
      have hc1 : twoScalars T i1 = 1 := by
        simp [twoScalars, i1]
      rw [hs0, hs1, hc0, hc1, map_one, one_pow, one_pow, div_one, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val, NNReal.coe_pow, NNReal.coe_pow, T.normalizedAbsUnits_coe,
        uniformizer_abs, ← pow_mul, inv_pow, zpow_neg, zpow_natCast]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (0 : ℕ) < 1
      omega
    · intro j hj hj1
      have hij : i0 < j := (Finset.mem_filter.mp hj).2
      have hij' : 0 < j.val := hij
      exact absurd (Fin.ext (by have := hlen j; change j.val = 1; omega)) hj1
  · intro i _ hi0
    apply Finset.prod_eq_one
    intro j hj
    have hij : i < j := (Finset.mem_filter.mp hj).2
    have hij' : i.val < j.val := hij
    have hi : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    have := hlen i
    have := hlen j
    omega
  · intro h
    exact absurd (Finset.mem_univ i0) h

/-- An upper-weakly-contracting tuple has monotone normalized absolute values. -/
theorem monotone_abs_of_isWeaklyContracting {N : ℕ} (B : BlockShape N)
    (c : Fin B.length → F.Carrierˣ) (hc : B.IsWeaklyContracting T c) :
    Monotone (fun l => T.normalizedAbs (c l : F.Carrier)) := by
  intro l l' hll'
  rcases hll'.lt_or_eq with hlt | heq
  · have h := hc l l' hlt
    rw [BlockShape.blockScalarRatio_apply, T.normalizedAbsUnits_coe] at h
    have hpos : 0 < T.normalizedAbs (c l' : F.Carrier) := by
      rw [← T.normalizedAbsUnits_coe]
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    have hmul : T.normalizedAbs ((c l * (c l')⁻¹ : F.Carrierˣ) : F.Carrier) =
        T.normalizedAbs (c l : F.Carrier) / T.normalizedAbs (c l' : F.Carrier) := by
      rw [← T.normalizedAbsUnits_coe, ← T.normalizedAbsUnits_coe, ← T.normalizedAbsUnits_coe,
        map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul,
        NNReal.coe_inv, div_eq_mul_inv]
    rw [hmul, div_le_one hpos] at h
    exact h
  · rw [heq]

/-! ### Eigenvalues of compressions by strictly contracting block scalars -/

section Eigenvalue

variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The upper generalized-exponent hypothesis of the chamber statement. -/
def UpperExponentHypothesis (ρ : Representation ℂ (C.Levi F.Carrier) V) : Prop :=
  letI := T.topology
  ∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
    IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) →
    IsGeneralizedEigencharacter
      ((T.normalizedRefinedJacquet C D ρ).comp
        ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
          ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
    ∀ a : Fin (C.flatten D).length → F.Carrierˣ,
      (∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
        T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) →
      ‖(ψ a : ℂ)‖ ≤ 1

/-- Flattened coordinates of a nested scalar tuple. -/
def flatScalars (D : BlockRefinement C) (c : ∀ i, Fin (D i).length → F.Carrierˣ) :
    Fin (C.flatten D).length → F.Carrierˣ :=
  fun y => c ((C.flattenBlockEquiv D).symm y).1 ((C.flattenBlockEquiv D).symm y).2

theorem flatScalars_apply (D : BlockRefinement C) (c : ∀ i, Fin (D i).length → F.Carrierˣ)
    (i : Fin C.length) (l : Fin (D i).length) :
    flatScalars C D c (C.flattenBlockEquiv D ⟨i, l⟩) = c i l := by
  unfold flatScalars
  rw [Equiv.symm_apply_apply]

theorem flattenedLeviEquiv_flatScalars_val (D : BlockRefinement C)
    (c : ∀ i, Fin (D i).length → F.Carrierˣ) :
    (flattenedLeviEquiv F.Carrier C D
        ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))).val =
      fun i => (D i).blockScalar F.Carrier (c i) := by
  funext i
  rw [Geometric.flattenedLeviEquiv_blockScalarLevi_apply]
  congr 1
  funext l
  exact flatScalars_apply C D c i l

theorem blockScalars_mem_refinedLevi (D : BlockRefinement C)
    (c : ∀ i, Fin (D i).length → F.Carrierˣ) :
    (fun i => (D i).blockScalar F.Carrier (c i) : C.Levi F.Carrier) ∈
      refinedLevi F.Carrier C D :=
  (Subgroup.mem_pi _).mpr fun i _ => (D i).blockScalar_mem_leviSubgroup F.Carrier (c i)

theorem blockScalars_commute_refinedLevi (D : BlockRefinement C)
    (c : ∀ i, Fin (D i).length → F.Carrierˣ) (m : C.Levi F.Carrier)
    (hm : m ∈ refinedLevi F.Carrier C D) :
    (fun i => (D i).blockScalar F.Carrier (c i) : C.Levi F.Carrier) * m =
      m * (fun i => (D i).blockScalar F.Carrier (c i)) := by
  funext i
  change (D i).blockScalar F.Carrier (c i) * m i = m i * (D i).blockScalar F.Carrier (c i)
  have hmi : m i ∈ (D i).leviSubgroup F.Carrier := (Subgroup.mem_pi _).mp hm i (Set.mem_univ i)
  obtain ⟨mi, hmi⟩ := hmi
  rw [← hmi]
  change (D i).leviEmbedding F.Carrier ((D i).blockScalarLevi F.Carrier (c i)) *
      (D i).leviEmbedding F.Carrier mi =
    (D i).leviEmbedding F.Carrier mi *
      (D i).leviEmbedding F.Carrier ((D i).blockScalarLevi F.Carrier (c i))
  rw [← map_mul, ← map_mul, (D i).blockScalarLevi_commute]

/-- Every eigenvalue of compression by a strictly contracting block-scalar tuple
on compact-open fixed vectors is bounded by the square root of the refined
modulus of that tuple. -/
theorem norm_eigenvalue_le :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V) (hadm : IsAdmissible ρ),
      UpperExponentHypothesis T C ρ →
      ∀ (K : ∀ j, OpenSubgroup (GeneralLinear (C.size j) F.Carrier))
        (hK : ∀ j, IsCompact (K j : Set (GeneralLinear (C.size j) F.Carrier)))
        (D : BlockRefinement C), (∀ i, (D i).HasBlockIwahoriFactorization T (K i)) →
      ∀ (c : ∀ i, Fin (D i).length → F.Carrierˣ), (∀ i, (D i).IsStrictlyContracting T (c i)) →
      ∀ (μ : ℂ) (x : fixedVectors ρ (CuspidalSupport.leviPiOpenSubgroup T C K).toSubgroup),
        x ≠ 0 →
        Jacquet.compressedAction ρ hadm.1 (CuspidalSupport.leviPiOpenSubgroup T C K)
            (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK)
            (fun i => (D i).blockScalar F.Carrier (c i)) x = μ • x →
        ‖μ‖ ≤ Real.sqrt ((T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
          ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))) : ℝ≥0) : ℝ) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hadm hexp K hK D hfac c hc μ x hx hμ
  classical
  let KP := CuspidalSupport.leviPiOpenSubgroup T C K
  let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK
  let g : C.Levi F.Carrier := fun i => (D i).blockScalar F.Carrier (c i)
  let A := Jacquet.compressedAction ρ hadm.1 KP hKP g
  by_cases hμ0 : μ = 0
  · rw [hμ0, norm_zero]
    exact Real.sqrt_nonneg _
  have hpow : ∀ r : ℕ, (A ^ r) x = μ ^ r • x := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, Module.End.mul_apply]
      rw [hμ, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hxs : x ∈ Jacquet.stableImage ρ hadm.1 KP hKP g := by
    rw [Jacquet.mem_stableImage]
    intro r
    refine ⟨(μ ^ r)⁻¹ • x, ?_⟩
    rw [map_smul, hpow, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hμ0), one_smul]
  have hbij := Jacquet.refinedStableImageJacquetBijective F T C D V ρ hadm K hK hfac c hc
  let N := refinedUnipotent F.Carrier C D
  let M := refinedLevi F.Carrier C D
  let hMN : M ≤ Subgroup.normalizer N :=
    fun m hm => (refinedLeviNormalizer F.Carrier C D ⟨m, hm⟩).property
  let J := Jacquet.stableImageJacquetMap ρ hadm.1 KP hKP g N M hMN
  let Y := fixedVectors (Jacquet.action ρ N M hMN) (KP.toSubgroup.comap M.subtype)
  have hJx : (J ⟨x, hxs⟩ : Jacquet.Coinvariants ρ N) = Jacquet.mk ρ N (x : V) := rfl
  have hy0 : Jacquet.mk ρ N (x : V) ≠ 0 := by
    intro h
    have h' : J ⟨x, hxs⟩ = 0 := Subtype.ext (by rw [hJx, h]; rfl)
    have h0 := (injective_iff_map_eq_zero J).mp hbij.1 _ h'
    exact hx (congrArg Subtype.val h0)
  have hy0Y : Jacquet.mk ρ N (x : V) ∈ Y := (J ⟨x, hxs⟩).property
  have : FiniteDimensional ℂ (fixedVectors ρ KP.toSubgroup) := hadm.2 KP
  have : FiniteDimensional ℂ Y := LinearEquiv.finiteDimensional (LinearEquiv.ofBijective J hbij)
  have hgM : g ∈ M := blockScalars_mem_refinedLevi C D c
  have hcomp := (Jacquet.refinedUpperCompression F T C D V ρ hadm.1 K hK hfac).2 c
    (fun i => (hc i).weak) x
  have heig : Jacquet.action ρ N M hMN ⟨g, hgM⟩ (Jacquet.mk ρ N (x : V)) =
      μ • Jacquet.mk ρ N (x : V) := by
    rw [Jacquet.action_mk]
    change Jacquet.mk ρ N (ρ g (x : V)) = _
    rw [← hcomp]
    change Jacquet.mk ρ N ((A x : fixedVectors ρ KP.toSubgroup) : V) = _
    rw [hμ, Submodule.coe_smul, map_smul]
  let z := (flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
    ((C.flatten D).blockScalarLevi F.Carrier)
  let π := (T.normalizedRefinedJacquet C D ρ).comp z
  have hπ : ∀ (b : Fin (C.flatten D).length → F.Carrierˣ) (y : Jacquet.Coinvariants ρ N),
      π b y = (T.refinedLeviInverseHalfModulus C D (z b) : ℂ) •
        Jacquet.action ρ N M hMN (z b) y := by
    intro b y
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N y
    change T.normalizedRefinedJacquet C D ρ (z b) (refinedJacquetMk C D ρ v) = _
    rw [T.normalizedRefinedJacquet_mk, Jacquet.action_mk]
  have hzval : ∀ b, ((z b : M) : C.Levi F.Carrier) =
      fun i => (D i).blockScalar F.Carrier (fun l => b (C.flattenBlockEquiv D ⟨i, l⟩)) :=
    fun b => funext fun i => Geometric.flattenedLeviEquiv_blockScalarLevi_apply F.Carrier C D b i
  have hzcomm : ∀ b (m : M), z b * m = m * z b := by
    intro b m
    apply Subtype.ext
    change ((z b : M) : C.Levi F.Carrier) * m = m * (z b : M)
    rw [hzval b]
    exact blockScalars_commute_refinedLevi (F := F) C D
      (fun i l => b (C.flattenBlockEquiv D ⟨i, l⟩)) m m.property
  have hactcomm : ∀ b (m : M) (y : Jacquet.Coinvariants ρ N),
      Jacquet.action ρ N M hMN (z b) (Jacquet.action ρ N M hMN m y) =
        Jacquet.action ρ N M hMN m (Jacquet.action ρ N M hMN (z b) y) := by
    intro b m y
    rw [← Module.End.mul_apply, ← map_mul, hzcomm, map_mul, Module.End.mul_apply]
  let E : Submodule ℂ (Jacquet.Coinvariants ρ N) :=
    Y ⊓ Module.End.eigenspace (Jacquet.action ρ N M hMN ⟨g, hgM⟩) μ
  have hEπ : ∀ b, ∀ y ∈ E, π b y ∈ E := by
    intro b y hy
    obtain ⟨hyY, hyE⟩ := Submodule.mem_inf.mp hy
    rw [hπ]
    refine Submodule.smul_mem _ _ (Submodule.mem_inf.mpr ⟨?_, ?_⟩)
    · intro h
      have hh := hyY h
      change Jacquet.action ρ N M hMN h.val y = y at hh
      change Jacquet.action ρ N M hMN h.val (Jacquet.action ρ N M hMN (z b) y) =
        Jacquet.action ρ N M hMN (z b) y
      rw [← hactcomm b h.val y, hh]
    · rw [Module.End.mem_eigenspace_iff] at hyE ⊢
      rw [← hactcomm b ⟨g, hgM⟩ y, hyE, map_smul]
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
  have hy0E : Jacquet.mk ρ N (x : V) ∈ E :=
    Submodule.mem_inf.mpr ⟨hy0Y, (Module.End.mem_eigenspace_iff).mpr heig⟩
  have : Nontrivial E := ⟨⟨⟨_, hy0E⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  let f : (Fin (C.flatten D).length → F.Carrierˣ) → Module.End ℂ E :=
    fun b => (π b).restrict (hEπ b)
  have hfc : ∀ b b', Commute (f b) (f b') := by
    intro b b'
    refine LinearMap.ext fun w => Subtype.ext ?_
    change π b (π b' w) = π b' (π b w)
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  obtain ⟨w, hw0, hw⟩ := EndomorphismBound.exists_common_eigenvector f hfc
  have hw' : ∀ b, ∃ c' : ℂ, π b (w : Jacquet.Coinvariants ρ N) =
      c' • (w : Jacquet.Coinvariants ρ N) := by
    intro b
    obtain ⟨c', hc'⟩ := hw b
    exact ⟨c', congrArg Subtype.val hc'⟩
  have hwne : (w : Jacquet.Coinvariants ρ N) ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨χ, hχ⟩ := EndomorphismBound.exists_character_of_forall_eigen π hwne hw'
  have : IsModuleTopology (Padic p) F.Carrier := T.moduleTopology
  have : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  have hzcont : Continuous z := by
    have hb : Continuous ((C.flatten D).blockScalarLevi F.Carrier) :=
      continuous_pi fun j =>
        (GeneralLinear.scalarContinuous (n := (C.flatten D).size j)).continuous.comp
          (continuous_apply j)
    exact (flattenedLeviEquivContinuous F.Carrier C D).continuous.comp hb
  have hπsmooth : IsSmooth π :=
    isSmooth_comp z hzcont (T.isSmooth_normalizedRefinedJacquet C D hadm.1)
  obtain ⟨U, hU⟩ := hπsmooth (w : Jacquet.Coinvariants ρ N)
  have hopen : IsOpen (χ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) := by
    apply Subgroup.isOpen_mono (H₁ := U.toSubgroup) _ U.isOpen
    intro u hu
    change χ u = 1
    apply Units.ext
    apply smul_left_injective ℂ hwne
    change (χ u : ℂ) • (w : Jacquet.Coinvariants ρ N) = (1 : ℂ) • (w : Jacquet.Coinvariants ρ N)
    rw [← hχ, one_smul]
    exact hU ⟨u, hu⟩
  have hgen : IsGeneralizedEigencharacter π χ :=
    isGeneralizedEigencharacter_of_eigenvector π χ hwne hχ
  have hmono : ∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
      T.normalizedAbs (flatScalars C D c (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier)) := by
    intro j
    simp only [flatScalars_apply]
    exact monotone_abs_of_isWeaklyContracting T (D j) (c j) (hc j).weak
  have hle := hexp D χ hopen hgen (flatScalars C D c) hmono
  have hzb0 : z (flatScalars C D c) = ⟨g, hgM⟩ :=
    Subtype.ext (flattenedLeviEquiv_flatScalars_val C D c)
  have hwE := Submodule.mem_inf.mp w.property
  have hweig : Jacquet.action ρ N M hMN ⟨g, hgM⟩ (w : Jacquet.Coinvariants ρ N) =
      μ • (w : Jacquet.Coinvariants ρ N) := Module.End.mem_eigenspace_iff.mp hwE.2
  have hχb0 : (χ (flatScalars C D c) : ℂ) =
      (T.refinedLeviInverseHalfModulus C D ⟨g, hgM⟩ : ℂ) * μ := by
    apply smul_left_injective ℂ hwne
    change (χ (flatScalars C D c) : ℂ) • (w : Jacquet.Coinvariants ρ N) =
      ((T.refinedLeviInverseHalfModulus C D ⟨g, hgM⟩ : ℂ) * μ) • (w : Jacquet.Coinvariants ρ N)
    rw [← hχ, hπ, hzb0, hweig, smul_smul]
  rw [hχb0, T.refinedLeviInverseHalfModulus_apply, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] at hle
  have hmod : T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
      ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))) =
      T.refinedLeviModulus C D ⟨g, hgM⟩ := by
    change T.refinedLeviModulus C D (z (flatScalars C D c)) = _
    rw [hzb0]
  rw [hmod, ← Real.coe_sqrt]
  have hpos : 0 < ((NNReal.sqrt (T.refinedLeviModulus C D ⟨g, hgM⟩ : ℝ≥0) : ℝ≥0) : ℝ) := by
    apply NNReal.coe_pos.mpr
    apply NNReal.sqrt_pos.mpr
    exact pos_iff_ne_zero.mpr (Units.ne_zero _)
  rw [inv_mul_le_iff₀ hpos, mul_one] at hle
  exact hle

end Eigenvalue

/-! ### Fundamental coweights of a product Levi -/

section Fundamental

variable {n : ℕ} (C : BlockShape n)

/-- Fundamental coweights: an outer block `j` and `t < C.size j - 1`, giving `k = t + 1`. -/
abbrev FundIndex := Σ j : Fin C.length, Fin (C.size j - 1)

theorem fundIndex_lt (s : FundIndex C) : s.2.val + 1 < C.size s.1 := by
  have := s.2.isLt
  omega

/-- The refinement `(k, C.size j - k)` of block `j`, all other blocks left whole. -/
def fundRefinement (s : FundIndex C) : BlockRefinement C :=
  Function.update (fun j' => oneBlock (C.size j') (C.positive j')) s.1
    (twoBlock (C.size s.1) (s.2.val + 1) (Nat.succ_pos _) (fundIndex_lt C s))

/-- The scalars `(ϖ, 1)` in block `j` and `1` elsewhere. -/
def fundScalars (s : FundIndex C) :
    ∀ i, Fin (fundRefinement C s i).length → F.Carrierˣ :=
  fun i l => if i = s.1 then twoScalars T l else 1

/-- The fundamental coweight as a family of integer tuples. -/
def fundTuple (s : FundIndex C) : ∀ j, Fin (C.size j) → ℤ :=
  fun j => if j = s.1 then fund (C.size j) (s.2.val + 1) else 0

/-- The Levi element with diagonal blocks `diag(ϖ^(lam j))`. -/
def leviRep (lam : ∀ j, Fin (C.size j) → ℤ) : C.Levi F.Carrier :=
  fun j => CartanQuotient.representative T (lam j)

theorem representative_zero (N : ℕ) : CartanQuotient.representative T (0 : Fin N → ℤ) = 1 := by
  apply Units.ext
  rw [CartanQuotient.representative, Iwasawa.torus_val]
  simp

theorem fundRefinement_length_of_ne (s : FundIndex C) {i : Fin C.length} (h : i ≠ s.1) :
    (fundRefinement C s i).length = 1 := by
  rw [fundRefinement, Function.update_of_ne h]
  rfl

theorem fundScalars_isStrictlyContracting (s : FundIndex C) (i : Fin C.length) :
    (fundRefinement C s i).IsStrictlyContracting T (fundScalars T C s i) := by
  obtain ⟨j, t⟩ := s
  by_cases h : i = j
  · subst h
    have hc : fundScalars T C ⟨i, t⟩ i = twoScalars T := funext fun l => by simp [fundScalars]
    rw [hc]
    exact twoBlock_isStrictlyContracting T _ _ _ _ _ (Function.update_self _ _ _)
  · exact isStrictlyContracting_of_length_eq_one T _ (fundRefinement_length_of_ne C ⟨j, t⟩ h) _

theorem fundScalars_blockScalar (s : FundIndex C) :
    (fun i => (fundRefinement C s i).blockScalar F.Carrier (fundScalars T C s i) :
      C.Levi F.Carrier) = leviRep T C (fundTuple C s) := by
  funext i
  obtain ⟨j, t⟩ := s
  by_cases h : i = j
  · subst h
    have hc : fundScalars T C ⟨i, t⟩ i = twoScalars T := funext fun l => by simp [fundScalars]
    rw [hc, twoBlock_blockScalar T (C.size i) (t.val + 1) (Nat.succ_pos _)
      (fundIndex_lt C ⟨i, t⟩) (fundRefinement C ⟨i, t⟩ i) (Function.update_self _ _ _)]
    simp [leviRep, fundTuple]
  · have hc : fundScalars T C ⟨j, t⟩ i = 1 := funext fun l => by simp [fundScalars, h]
    rw [hc, BlockShape.blockScalar_one]
    simp [leviRep, fundTuple, h, representative_zero]

theorem fund_refinedLeviModulus (s : FundIndex C) :
    ((T.refinedLeviModulus C (fundRefinement C s) (flattenedLeviEquiv F.Carrier C
        (fundRefinement C s) ((C.flatten (fundRefinement C s)).blockScalarLevi F.Carrier
          (flatScalars C (fundRefinement C s) (fundScalars T C s)))) : ℝ≥0) : ℝ) =
      (T.residueCardinality : ℝ) ^
        (-(((s.2.val + 1) * (C.size s.1 - (s.2.val + 1)) : ℕ) : ℤ)) := by
  obtain ⟨j, t⟩ := s
  rw [T.refinedLeviModulus_apply]
  have hblock : ∀ i, PadicField.TopologicalData.refinedLeviBlock C (fundRefinement C ⟨j, t⟩) i
      (flattenedLeviEquiv F.Carrier C (fundRefinement C ⟨j, t⟩)
        ((C.flatten (fundRefinement C ⟨j, t⟩)).blockScalarLevi F.Carrier
          (flatScalars C (fundRefinement C ⟨j, t⟩) (fundScalars T C ⟨j, t⟩)))) =
      (fundRefinement C ⟨j, t⟩ i).blockScalarLevi F.Carrier (fundScalars T C ⟨j, t⟩ i) := by
    intro i
    rw [PadicField.TopologicalData.refinedLeviBlock_flattenedLeviEquiv,
      Geometric.flattenedLeviProductEquiv_blockScalarLevi]
    congr 1
    funext l
    exact flatScalars_apply C _ _ i l
  simp only [hblock]
  rw [Finset.prod_eq_single j]
  · have hc : fundScalars T C ⟨j, t⟩ j = twoScalars T := funext fun l => by simp [fundScalars]
    rw [hc]
    exact twoBlock_leviModulus T _ _ _ _ _ (Function.update_self _ _ _)
  · intro i _ hi
    exact leviModulus_of_length_eq_one T _ (fundRefinement_length_of_ne C ⟨j, t⟩ hi) _
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem delta_zero (N : ℕ) : CartanQuotient.delta T (0 : Fin N → ℤ) = 1 := by
  simp [CartanQuotient.delta, CartanQuotient.degree]

/-- The radial weight of a fundamental coweight. -/
def fundWeight (s : FundIndex C) : ℝ := ∏ j, CartanQuotient.delta T (fundTuple C s j)

theorem fundWeight_eq (s : FundIndex C) :
    fundWeight T C s = (T.residueCardinality : ℝ) ^
      (-(((s.2.val + 1) * (C.size s.1 - (s.2.val + 1)) : ℕ) : ℤ)) := by
  obtain ⟨j, t⟩ := s
  unfold fundWeight
  rw [Finset.prod_eq_single j]
  · simp only [fundTuple, ↓reduceIte]
    exact delta_fund T _ _ (fundIndex_lt C ⟨j, t⟩).le
  · intro i _ hi
    simp only [fundTuple, hi, ↓reduceIte]
    exact delta_zero T _
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem fundWeight_pos (s : FundIndex C) : 0 < fundWeight T C s := by
  rw [fundWeight_eq]
  have := residueCardinality_gt_one_real T
  positivity

theorem fundWeight_lt_one (s : FundIndex C) : fundWeight T C s < 1 := by
  rw [fundWeight_eq]
  have hq := residueCardinality_gt_one_real T
  have hpos : 0 < (s.2.val + 1) * (C.size s.1 - (s.2.val + 1)) := by
    have := fundIndex_lt C s
    apply Nat.mul_pos <;> omega
  apply zpow_lt_one_of_neg₀ hq
  omega

end Fundamental

/-! ### Compression along the antidominant chamber -/

section Compression

variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Every eigenvalue of compression by a fundamental coweight is bounded by the
square root of its radial weight. -/
theorem fund_norm_eigenvalue_le :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V) (hadm : IsAdmissible ρ),
      UpperExponentHypothesis T C ρ →
      ∀ (K : ∀ j, OpenSubgroup (GeneralLinear (C.size j) F.Carrier))
        (hK : ∀ j, IsCompact (K j : Set (GeneralLinear (C.size j) F.Carrier))),
        (∀ j (B : BlockShape (C.size j)), B.HasBlockIwahoriFactorization T (K j)) →
      ∀ (s : FundIndex C) (μ : ℂ)
        (x : fixedVectors ρ (CuspidalSupport.leviPiOpenSubgroup T C K).toSubgroup), x ≠ 0 →
        Jacquet.compressedAction ρ hadm.1 (CuspidalSupport.leviPiOpenSubgroup T C K)
            (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK)
            (leviRep T C (fundTuple C s)) x = μ • x →
        ‖μ‖ ≤ Real.sqrt (fundWeight T C s) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hadm hexp K hK hfac s μ x hx hμ
  rw [← fundScalars_blockScalar T C s] at hμ
  have h := norm_eigenvalue_le T C ρ hadm hexp K hK (fundRefinement C s) (fun i => hfac i _)
    (fundScalars T C s) (fundScalars_isStrictlyContracting T C s) μ x hx hμ
  rwa [fund_refinedLeviModulus, ← fundWeight_eq] at h

/-- The Borel refinement: singleton blocks in every outer block. -/
def borelRefinement : BlockRefinement C := fun j => BlockShape.singletons (C.size j)

/-- Uniformizer powers as singleton-block scalars. -/
def borelScalars (lam : ∀ j, Fin (C.size j) → ℤ) :
    ∀ j, Fin (borelRefinement C j).length → F.Carrierˣ :=
  fun j i => LocalFactor.PadicAbelian.uniformizerUnit T ^ lam j i

theorem borelScalars_blockScalar (lam : ∀ j, Fin (C.size j) → ℤ) :
    (fun j => (borelRefinement C j).blockScalar F.Carrier (borelScalars T C lam j) :
      C.Levi F.Carrier) = leviRep T C lam := by
  funext j
  apply Units.ext
  rw [blockScalar_val, leviRep, CartanQuotient.representative, Iwasawa.torus_val]
  congr 1
  funext x
  have hx : (BlockShape.singletons (C.size j)).indexEquiv.symm x = ⟨x, 0⟩ :=
    (Equiv.symm_apply_eq _).mpr (BlockShape.singletons_indexEquiv_apply x 0).symm
  change ((LocalFactor.PadicAbelian.uniformizerUnit T ^
      lam j ((BlockShape.singletons (C.size j)).indexEquiv.symm x).1 : F.Carrierˣ) : F.Carrier) = _
  rw [hx]

theorem borelScalars_isWeaklyContracting (lam : ∀ j, Fin (C.size j) → ℤ)
    (hlam : ∀ j, Antitone (lam j)) (j : Fin C.length) :
    (borelRefinement C j).IsWeaklyContracting T (borelScalars T C lam j) := by
  intro i i' hii'
  rw [BlockShape.blockScalarRatio_apply, T.normalizedAbsUnits_coe]
  simp only [borelScalars]
  rw [← zpow_neg, ← zpow_add, LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs]
  have h := hlam j hii'.le
  apply zpow_le_one_of_nonpos₀ (residueCardinality_gt_one_real T).le
  change lam j i' ≤ lam j i at h
  omega

theorem borelScalars_add (lam lam' : ∀ j, Fin (C.size j) → ℤ) :
    borelScalars T C (lam + lam') = borelScalars T C lam * borelScalars T C lam' := by
  funext j i
  change LocalFactor.PadicAbelian.uniformizerUnit T ^ (lam j i + lam' j i) =
    LocalFactor.PadicAbelian.uniformizerUnit T ^ lam j i *
      LocalFactor.PadicAbelian.uniformizerUnit T ^ lam' j i
  rw [zpow_add]

theorem leviRep_zero : leviRep T C 0 = 1 := by
  funext j
  exact representative_zero T _

/-- Compression is multiplicative along blockwise antitone exponent tuples. -/
theorem compressedAction_leviRep_add :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V) (hρ : IsSmooth ρ)
      (K : ∀ j, OpenSubgroup (GeneralLinear (C.size j) F.Carrier))
      (hK : ∀ j, IsCompact (K j : Set (GeneralLinear (C.size j) F.Carrier))),
      (∀ j (B : BlockShape (C.size j)), B.HasBlockIwahoriFactorization T (K j)) →
      ∀ lam lam' : ∀ j, Fin (C.size j) → ℤ, (∀ j, Antitone (lam j)) → (∀ j, Antitone (lam' j)) →
        Jacquet.compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T C K)
            (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK) (leviRep T C (lam + lam')) =
          Jacquet.compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T C K)
              (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK) (leviRep T C lam) *
            Jacquet.compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T C K)
              (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK) (leviRep T C lam') := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hρ K hK hfac lam lam' hlam hlam'
  have h := (Jacquet.refinedUpperCompression F T C (borelRefinement C) V ρ hρ K hK
    (fun i => hfac i _)).1 (borelScalars T C lam) (borelScalars T C lam')
    (borelScalars_isWeaklyContracting T C lam hlam)
    (borelScalars_isWeaklyContracting T C lam' hlam')
  rw [← borelScalars_add, borelScalars_blockScalar, borelScalars_blockScalar,
    borelScalars_blockScalar] at h
  exact h

theorem antitone_nsmul {N : ℕ} {f : Fin N → ℤ} (hf : Antitone f) (m : ℕ) : Antitone (m • f) := by
  intro x y hxy
  simp only [Pi.smul_apply, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hf hxy) (by positivity)

/-- Compression by a multiple of an antitone tuple is the power of its compression. -/
theorem compressedAction_leviRep_nsmul :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V) (hρ : IsSmooth ρ)
      (K : ∀ j, OpenSubgroup (GeneralLinear (C.size j) F.Carrier))
      (hK : ∀ j, IsCompact (K j : Set (GeneralLinear (C.size j) F.Carrier))),
      (∀ j (B : BlockShape (C.size j)), B.HasBlockIwahoriFactorization T (K j)) →
      ∀ f : ∀ j, Fin (C.size j) → ℤ, (∀ j, Antitone (f j)) → ∀ m : ℕ,
        Jacquet.compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T C K)
            (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK) (leviRep T C (m • f)) =
          Jacquet.compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T C K)
              (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK) (leviRep T C f) ^ m := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hρ K hK hfac f hf m
  induction m with
  | zero =>
    rw [zero_nsmul, leviRep_zero, Jacquet.compressedAction_one, pow_zero]
    rfl
  | succ m ih =>
    rw [succ_nsmul, compressedAction_leviRep_add T C ρ hρ K hK hfac (m • f) f
      (fun j => antitone_nsmul (hf j) m) hf, ih, pow_succ]

end Compression

/-! ### Decomposition of the normalized chamber -/

section Decomposition

variable {n : ℕ} (C : BlockShape n)

theorem sum_range_telescope (f : ℕ → ℤ) (x : ℕ) :
    ∀ L, x ≤ L → f x - f L =
      ∑ t ∈ Finset.range L, (if x ≤ t then f t - f (t + 1) else 0) := by
  intro L
  induction L with
  | zero =>
    intro hx
    have : x = 0 := by omega
    subst this
    simp
  | succ L ih =>
    intro hx
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge L x with hLx | hxL
    · have hxL : x = L + 1 := by omega
      subst hxL
      rw [sub_self, ite_eq_right (by omega), add_zero]
      symm
      apply Finset.sum_eq_zero
      intro t ht
      rw [ite_eq_right]
      have := Finset.mem_range.mp ht
      omega
    · rw [ite_eq_left hxL, ← ih hxL]
      ring

/-- A normalized tuple is a nonnegative combination of fundamental coweights,
with the successive differences as coefficients. -/
theorem normalized_eq_sum_fund {N : ℕ} (μ : Fin N → ℤ) (hμ : CartanQuotient.Normalized μ)
    (x : Fin N) :
    μ x = ∑ t : Fin (N - 1),
      ((μ ⟨t.val, by omega⟩ - μ ⟨t.val + 1, by omega⟩).toNat : ℤ) * fund N (t.val + 1) x := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by have := x.isLt; omega⟩
  obtain ⟨hanti, hlast⟩ := (CartanQuotient.normalized_iff_antitone_last_eq_zero m μ).mp hμ
  let f : ℕ → ℤ := fun k => if h : k < m + 1 then μ ⟨k, h⟩ else 0
  have hfx : f x.val = μ x := by
    change (if h : x.val < m + 1 then μ ⟨x.val, h⟩ else 0) = μ x
    rw [dite_eq_left x.isLt]
  have hfm : f m = 0 := by
    simp only [f, show m < m + 1 by omega, ↓reduceDIte]
    exact hlast
  have htel := sum_range_telescope f x.val m (by have := x.isLt; omega)
  rw [hfx, hfm, sub_zero] at htel
  rw [htel, ← Fin.sum_univ_eq_sum_range (fun t => if x.val ≤ t then f t - f (t + 1) else 0) m]
  apply Finset.sum_congr (by simp) 
  intro t _
  have ht : t.val < m := t.isLt
  have hft : f t.val = μ ⟨t.val, by omega⟩ := by
    change (if h : t.val < m + 1 then μ ⟨t.val, h⟩ else 0) = _
    rw [dite_eq_left (by omega)]
  have hft1 : f (t.val + 1) = μ ⟨t.val + 1, by omega⟩ := by
    change (if h : t.val + 1 < m + 1 then μ ⟨t.val + 1, h⟩ else 0) = _
    rw [dite_eq_left (by omega)]
  have hnn : 0 ≤ μ ⟨t.val, by omega⟩ - μ ⟨t.val + 1, by omega⟩ := by
    apply sub_nonneg.mpr
    apply hanti
    change t.val ≤ t.val + 1
    omega
  rw [hft, hft1, Int.toNat_of_nonneg hnn]
  unfold fund
  by_cases hxt : x.val ≤ t.val
  · rw [ite_eq_left hxt, ite_eq_left (by omega), mul_one]
  · rw [ite_eq_right hxt, ite_eq_right (by omega), mul_zero]

/-- Coefficients of a blockwise normalized family along the fundamental coweights. -/
def fundCoeff (lam : ∀ j, Fin (C.size j) → ℤ) (s : FundIndex C) : ℕ :=
  (lam s.1 ⟨s.2.val, by have := s.2.isLt; omega⟩ -
    lam s.1 ⟨s.2.val + 1, by have := s.2.isLt; omega⟩).toNat

theorem fundTuple_antitone (s : FundIndex C) (j : Fin C.length) : Antitone (fundTuple C s j) := by
  unfold fundTuple
  split_ifs
  · exact fund_antitone _ _
  · exact antitone_const

theorem normalized_eq_sum_fundTuple (lam : ∀ j, Fin (C.size j) → ℤ)
    (hlam : ∀ j, CartanQuotient.Normalized (lam j)) :
    lam = ∑ s : FundIndex C, fundCoeff C lam s • fundTuple C s := by
  funext j x
  rw [Finset.sum_apply, Finset.sum_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · rw [normalized_eq_sum_fund (lam j) (hlam j) x]
    apply Finset.sum_congr rfl
    intro t _
    simp [fundTuple, fundCoeff]
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro t _
    simp [fundTuple, Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem antitone_sum_fundTuple (S : Finset (FundIndex C)) (m : FundIndex C → ℕ)
    (j : Fin C.length) : Antitone ((∑ s ∈ S, m s • fundTuple C s) j) := by
  classical
  induction S using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    intro a b _
    simp
  | @insert s S hs ih =>
    rw [Finset.sum_insert hs, Pi.add_apply]
    exact (antitone_nsmul (fundTuple_antitone C s j) (m s)).add ih

theorem degree_add {N : ℕ} (μ ν : Fin N → ℤ) :
    CartanQuotient.degree (μ + ν) = CartanQuotient.degree μ + CartanQuotient.degree ν := by
  unfold CartanQuotient.degree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply]
  ring

theorem degree_nsmul {N : ℕ} (μ : Fin N → ℤ) (m : ℕ) :
    CartanQuotient.degree (m • μ) = m * CartanQuotient.degree μ := by
  unfold CartanQuotient.degree
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring

theorem delta_add {N : ℕ} (μ ν : Fin N → ℤ) :
    CartanQuotient.delta T (μ + ν) = CartanQuotient.delta T μ * CartanQuotient.delta T ν := by
  have hq : (T.residueCardinality : ℝ) ≠ 0 := (zero_lt_one.trans (residueCardinality_gt_one_real T)).ne'
  unfold CartanQuotient.delta
  rw [degree_add, neg_add, zpow_add₀ hq]

theorem delta_nsmul {N : ℕ} (μ : Fin N → ℤ) (m : ℕ) :
    CartanQuotient.delta T (m • μ) = CartanQuotient.delta T μ ^ m := by
  unfold CartanQuotient.delta
  rw [degree_nsmul, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem delta_sum {N : ℕ} {ι : Type*} (S : Finset ι) (g : ι → Fin N → ℤ) :
    CartanQuotient.delta T (∑ s ∈ S, g s) = ∏ s ∈ S, CartanQuotient.delta T (g s) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using delta_zero T N
  | @insert s S hs ih => rw [Finset.sum_insert hs, Finset.prod_insert hs, delta_add, ih]

/-- The radial weights of a blockwise normalized family are the products of the
weights of its fundamental coweights. -/
theorem prod_delta_eq (lam : ∀ j, Fin (C.size j) → ℤ)
    (hlam : ∀ j, CartanQuotient.Normalized (lam j)) :
    ∏ j, CartanQuotient.delta T (lam j) =
      ∏ s : FundIndex C, fundWeight T C s ^ fundCoeff C lam s := by
  have hdec := normalized_eq_sum_fundTuple C lam hlam
  have hj : ∀ j, CartanQuotient.delta T (lam j) =
      ∏ s : FundIndex C, CartanQuotient.delta T (fundTuple C s j) ^ fundCoeff C lam s := by
    intro j
    conv_lhs => rw [hdec]
    rw [Finset.sum_apply, delta_sum]
    apply Finset.prod_congr rfl
    intro s _
    rw [Pi.smul_apply, delta_nsmul]
  simp only [hj]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro s _
  rw [Finset.prod_pow]
  rfl

end Decomposition

/-! ### The chamber bound -/

section Main

variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The chamber bound for an arbitrary admissible carrier satisfying the upper
generalized-exponent hypothesis. -/
theorem chamber_bound :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V), IsAdmissible ρ →
      UpperExponentHypothesis T C ρ →
      ∀ (ℓ : SmoothDual ρ) (v : V) (η : ℝ), 0 < η →
        ∃ c : ℝ, ∀ lam : ∀ j : Fin C.length, Fin (C.size j) → ℤ,
          (∀ j, CartanQuotient.Normalized (lam j)) →
          ‖matrixCoefficient ρ (ℓ : Module.Dual ℂ V) v (leviRep T C lam)‖ ≤
            c * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 - η) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hadm hexp ℓ v η hη
  classical
  obtain ⟨Kv, hKv⟩ := hadm.1 v
  obtain ⟨Kℓ, hKℓ⟩ := ℓ.property
  have hU : (Kv : Set (C.Levi F.Carrier)) ∩ (Kℓ : Set (C.Levi F.Carrier)) ∈
      nhds (1 : C.Levi F.Carrier) :=
    Filter.inter_mem Kv.mem_nhds_one Kℓ.mem_nhds_one
  obtain ⟨K, hKc, hfac, hKU⟩ := CuspidalSupport.exists_leviPiOpenSubgroup_subset_forall T C hU
  let KP := CuspidalSupport.leviPiOpenSubgroup T C K
  let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hKc
  let W := fixedVectors ρ KP.toSubgroup
  have : FiniteDimensional ℂ W := hadm.2 KP
  have hvW : v ∈ W := fun k => hKv ⟨k.val, (hKU k.property).1⟩
  let v0 : W := ⟨v, hvW⟩
  let φ : Module.Dual ℂ W := (ℓ : Module.Dual ℂ V).comp W.subtype
  have hℓK : (ℓ : Module.Dual ℂ V) ∈ fixedVectors ρ.dual KP.toSubgroup :=
    fun k => hKℓ ⟨k.val, (hKU k.property).2⟩
  let A : (∀ j, Fin (C.size j) → ℤ) → Module.End ℂ W :=
    fun lam => Jacquet.compressedAction ρ hadm.1 KP hKP (leviRep T C lam)
  have hcoef : ∀ lam, matrixCoefficient ρ (ℓ : Module.Dual ℂ V) v (leviRep T C lam) =
      φ (A lam v0) := by
    intro lam
    change (ℓ : Module.Dual ℂ V) (ρ (leviRep T C lam) v) =
      (ℓ : Module.Dual ℂ V) (Compact.averageMap ρ hadm.1 KP hKP (ρ (leviRep T C lam) v))
    rw [Compact.dual_averageMap_eq_of_mem_fixedVectors ρ hadm.1 KP hKP _ hℓK]
  -- Radii for the fundamental coweights.
  let r : FundIndex C → ℝ := fun s => fundWeight T C s ^ ((1 : ℝ) / 2 - η)
  have hr0r : ∀ s, Real.sqrt (fundWeight T C s) < r s := by
    intro s
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_lt_rpow_of_exponent_gt (fundWeight_pos T C s) (fundWeight_lt_one T C s)
      (by linarith)
  have hpow : ∀ s, ∃ c : ℝ, ∀ m : ℕ,
      EndomorphismBound.endNorm (A (fundTuple C s) ^ m) ≤ c * r s ^ m := fun s =>
    EndomorphismBound.exists_endNorm_pow_le (A (fundTuple C s)) (Real.sqrt_nonneg _) (hr0r s)
      (fun μ x hx hμ => fund_norm_eigenvalue_le T C ρ hadm hexp K hKc hfac s μ x hx hμ)
  choose cs hcs using hpow
  obtain ⟨Cφ, hCφ0, hCφ⟩ := EndomorphismBound.exists_apply_le_endNorm φ v0
  have hantiS : ∀ (m : FundIndex C → ℕ) (S : Finset (FundIndex C)) (j : Fin C.length),
      Antitone ((∑ s ∈ S, m s • fundTuple C s) j) := fun m S j =>
    antitone_sum_fundTuple C S m j
  have key : ∀ (m : FundIndex C → ℕ) (S : Finset (FundIndex C)),
      EndomorphismBound.endNorm (A (∑ s ∈ S, m s • fundTuple C s)) ≤
        EndomorphismBound.endNorm (A 0) * ∏ s ∈ S, (cs s * r s ^ m s) := by
    intro m S
    induction S using Finset.induction with
    | empty => simp
    | @insert s S hs ih =>
      rw [Finset.sum_insert hs, Finset.prod_insert hs]
      have hmul : A (m s • fundTuple C s + ∑ t ∈ S, m t • fundTuple C t) =
          A (fundTuple C s) ^ m s * A (∑ t ∈ S, m t • fundTuple C t) := by
        change Jacquet.compressedAction ρ hadm.1 KP hKP (leviRep T C _) = _
        rw [compressedAction_leviRep_add T C ρ hadm.1 K hKc hfac (m s • fundTuple C s)
          (∑ t ∈ S, m t • fundTuple C t)
          (fun j => antitone_nsmul (fundTuple_antitone C s j) (m s)) (hantiS m S),
          compressedAction_leviRep_nsmul T C ρ hadm.1 K hKc hfac (fundTuple C s)
            (fundTuple_antitone C s)]
      rw [hmul]
      have h1 := hcs s (m s)
      have h0 := EndomorphismBound.endNorm_nonneg (A (fundTuple C s) ^ m s)
      have h2 := EndomorphismBound.endNorm_nonneg (A (∑ t ∈ S, m t • fundTuple C t))
      calc EndomorphismBound.endNorm (A (fundTuple C s) ^ m s * A (∑ t ∈ S, m t • fundTuple C t))
          ≤ EndomorphismBound.endNorm (A (fundTuple C s) ^ m s) *
              EndomorphismBound.endNorm (A (∑ t ∈ S, m t • fundTuple C t)) :=
            EndomorphismBound.endNorm_mul_le _ _
        _ ≤ (cs s * r s ^ m s) *
              (EndomorphismBound.endNorm (A 0) * ∏ t ∈ S, (cs t * r t ^ m t)) :=
            mul_le_mul h1 ih h2 (h0.trans h1)
        _ = EndomorphismBound.endNorm (A 0) * ((cs s * r s ^ m s) * ∏ t ∈ S, (cs t * r t ^ m t)) := by
            ring
  refine ⟨Cφ * EndomorphismBound.endNorm (A 0) * ∏ s, cs s, fun lam hlam => ?_⟩
  have hdec := normalized_eq_sum_fundTuple C lam hlam
  have hbound := key (fundCoeff C lam) Finset.univ
  rw [← hdec] at hbound
  rw [hcoef]
  have hprod : ∏ s, (cs s * r s ^ fundCoeff C lam s) =
      (∏ s, cs s) * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 - η) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    have hw : ∀ s ∈ (Finset.univ : Finset (FundIndex C)),
        0 ≤ fundWeight T C s ^ fundCoeff C lam s := fun s _ =>
      pow_nonneg (fundWeight_pos T C s).le _
    have hd : ∀ j ∈ (Finset.univ : Finset (Fin C.length)), 0 ≤ CartanQuotient.delta T (lam j) :=
      fun j _ => (CartanQuotient.delta_pos T (lam j)).le
    calc ∏ s, r s ^ fundCoeff C lam s
        = ∏ s, (fundWeight T C s ^ fundCoeff C lam s) ^ ((1 : ℝ) / 2 - η) := by
          apply Finset.prod_congr rfl
          intro s _
          exact Real.rpow_pow_comm (fundWeight_pos T C s).le _ _
      _ = (∏ s, fundWeight T C s ^ fundCoeff C lam s) ^ ((1 : ℝ) / 2 - η) :=
          Real.finsetProd_rpow _ _ hw _
      _ = (∏ j, CartanQuotient.delta T (lam j)) ^ ((1 : ℝ) / 2 - η) := by
          rw [prod_delta_eq T C lam hlam]
      _ = ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 - η) :=
          (Real.finsetProd_rpow _ _ hd _).symm
  calc ‖φ (A lam v0)‖ ≤ Cφ * EndomorphismBound.endNorm (A lam) := hCφ (A lam)
    _ ≤ Cφ * (EndomorphismBound.endNorm (A 0) * ∏ s, (cs s * r s ^ fundCoeff C lam s)) :=
        mul_le_mul_of_nonneg_left hbound hCφ0
    _ = (Cφ * EndomorphismBound.endNorm (A 0) * ∏ s, cs s) *
          ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 - η) := by
        rw [hprod]
        ring

end Main

end Langlands.ProductLeviChamber

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Proof of the product-Levi chamber bound. -/
theorem glProductLeviChamberCoefficientBound :
    GLProductLeviChamberCoefficientBoundStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n C S hadm hexp ℓ v η hη
  exact ProductLeviChamber.chamber_bound T C S.ρ hadm hexp ℓ v η hη
