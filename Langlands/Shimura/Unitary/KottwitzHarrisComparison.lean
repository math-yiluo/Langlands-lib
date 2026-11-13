import Langlands.Shimura.Unitary.KottwitzFrobeniusPlaces
import Langlands.Shimura.Unitary.KottwitzLiftIndependence
import Langlands.Shimura.Unitary.KottwitzBaseChange

/-!
# Kottwitz's polynomial for Harris's signature

For the signature `(n - 1, 1)` at one real place `τ₀` and `(n, 0)` or `(0, n)` at the
others, the Frobenius operator `V(Φ_v)` is diagonal in the standard basis of
`W = ⨂_τ ⋀^{k_τ} Lⁿ`, and Kottwitz's polynomial is `∏_j (X - α β_j)`.
See the paired Markdown.
-/

noncomputable section

open Module exteriorPower Set.powersetCard Polynomial

namespace Langlands.Shimura.KottwitzDual

universe u v w uΩ

/-! ### The torus acts diagonally on the standard basis of `W` -/

section Weights

variable {L : Type v} [Field L] {n : ℕ}

theorem map_diagonal_ιMulti_basisFun (d : Fin n → L) {k : ℕ} (g : Fin k → Fin n) :
    exteriorPower.map k (Matrix.toLin' (Matrix.diagonal d))
        (ιMulti L k (fun j => Pi.basisFun L (Fin n) (g j))) =
      (∏ j, d (g j)) • ιMulti L k (fun j => Pi.basisFun L (Fin n) (g j)) := by
  rw [map_apply_ιMulti, ← AlternatingMap.map_smul_univ]
  congr 1
  funext j x
  simp only [Function.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal,
    Pi.basisFun_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs with hx
  · rw [hx]
  · simp

theorem exteriorPower_basisFun_apply {k : ℕ} (U : Set.powersetCard (Fin n) k) :
    (Pi.basisFun L (Fin n)).exteriorPower k U =
      ιMulti L k (fun j => Pi.basisFun L (Fin n) (Finset.orderEmbOfFin U.1 U.2 j)) := by
  rw [basis_apply, ιMulti_family, ofFinEmbEquiv_symm_apply]
  rfl

theorem prod_orderEmbOfFin {M : Type*} [CommMonoid M] {k : ℕ} (U : Set.powersetCard (Fin n) k)
    (d : Fin n → M) : ∏ j : Fin k, d (Finset.orderEmbOfFin U.1 U.2 j) = ∏ x ∈ U.1, d x := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ U.1 U.2]
  rw [Finset.prod_map]
  rfl

/-- `ρ_k(diag s)` acts on the basis vector `e_U` by `∏_{j ∉ U} s_j⁻¹`. -/
theorem wedgeRep_diagUnit_basis (s : Fin n → Lˣ) {k : ℕ} (U : Set.powersetCard (Fin n) k) :
    wedgeRep k (diagUnit s) ((Pi.basisFun L (Fin n)).exteriorPower k U) =
      ((∏ j, s j ^ (if j ∈ U.1 then (0 : ℤ) else -1) : Lˣ) : L) •
        (Pi.basisFun L (Fin n)).exteriorPower k U := by
  rw [wedgeRep_apply, diagUnit_val, exteriorPower_basisFun_apply, map_diagonal_ιMulti_basisFun,
    smul_smul, Matrix.det_diagonal, prod_orderEmbOfFin U (fun x => (s x : L))]
  congr 1
  have key : (∏ j, s j)⁻¹ * ∏ x ∈ U.1, s x =
      ∏ j, s j ^ (if j ∈ U.1 then (0 : ℤ) else -1) := by
    rw [← Fintype.prod_ite_mem U.1 s, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [← key]
  push_cast
  rfl

variable {S : Type u} [Fintype S]

/-- The weight `(a₀, (a_{τ,j}))` of the basis vector `⨂_τ e_{T_τ}` of `W`:
`a₀ = -1` and `a_{τ,j} = -1` for `j ∉ T_τ`, `0` for `j ∈ T_τ`. -/
def basisWeight {k : S → ℕ} (T : ∀ τ, Set.powersetCard (Fin n) (k τ)) :
    ℤ × (S → Fin n → ℤ) :=
  (-1, fun τ j => if j ∈ (T τ).1 then 0 else -1)

/-- The dual torus acts on the standard basis vector `⨂_τ e_{T_τ}` through its weight. -/
theorem dualRep_torusElement_basis (k : S → ℕ) (t : Lˣ × (S → Fin n → Lˣ))
    (T : ∀ τ, Set.powersetCard (Fin n) (k τ)) :
    dualRep k (torusElement t) (kottwitzBasis n L k T) =
      (cocharPairing t (basisWeight T) : L) • kottwitzBasis n L k T := by
  rw [kottwitzBasis, Basis.piTensorProduct_apply, dualRep_tprod]
  simp only [torusElement, wedgeRep_diagUnit_basis]
  rw [MultilinearMap.map_smul_univ, smul_smul]
  congr 1
  simp only [cocharPairing, basisWeight, Units.val_mul, Units.coe_prod, zpow_neg_one,
    Units.val_inv_eq_inv_val]

end Weights

/-! ### Frobenius on the standard basis for Harris's signature -/

section Frobenius

variable {L : Type v} [Field L] {n : ℕ}

/-- In `⋀⁰ Lⁿ` and `⋀ⁿ Lⁿ` the standard basis vector is the highest weight vector. -/
theorem exteriorPower_basisFun_eq_hwVector {k : ℕ} (hk : k ≤ n) (hk' : k = 0 ∨ k = n)
    (U : Set.powersetCard (Fin n) k) :
    (Pi.basisFun L (Fin n)).exteriorPower k U = hwVector k hk := by
  rw [exteriorPower_basisFun_apply, hwVector]
  have hU : ∀ x : Fin k, Fin.castLE hk x ∈ U.1 := by
    intro x
    rcases hk' with rfl | rfl
    · exact x.elim0
    · rw [Finset.eq_univ_of_card U.1 (by rw [U.2, Fintype.card_fin])]
      exact Finset.mem_univ _
  rw [← Finset.orderEmbOfFin_unique U.2 hU (Fin.strictMono_castLE hk)]

theorem exteriorPower_basisFun_coe_congr {S : Type u} {k : S → ℕ}
    (T : ∀ τ, Set.powersetCard (Fin n) (k τ)) {a b : S} (e : a = b) :
    (((Pi.basisFun L (Fin n)).exteriorPower (k a) (T a) : ⋀[L]^(k a) (Fin n → L)) :
        ExteriorAlgebra L (Fin n → L)) =
      (((Pi.basisFun L (Fin n)).exteriorPower (k b) (T b) : ⋀[L]^(k b) (Fin n → L)) :
        ExteriorAlgebra L (Fin n → L)) := by
  subst e
  rfl

variable {S : Type u} [Fintype S]
variable (h : S × Bool → ℕ) (hsum : ∀ τ, h (τ, true) + h (τ, false) = n)

/-- For Harris's signature (`k_τ ∈ {0, n}` away from `τ₀`), a Frobenius permutation fixing
`(τ₀, true)` fixes every standard basis vector of `W`. -/
theorem frobOp_kottwitzBasis (G : CMPerm S) (hG : ∀ x, h ((G : Equiv.Perm (S × Bool)) x) = h x)
    {τ0 : S} (hτ0 : ∀ τ, τ ≠ τ0 → h (τ, false) = 0 ∨ h (τ, false) = n)
    (hfix : (G : Equiv.Perm (S × Bool)) (τ0, true) = (τ0, true))
    (T : ∀ τ, Set.powersetCard (Fin n) (hodgeDegrees h τ)) :
    frobOp h hsum G hG (kottwitzBasis n L (hodgeDegrees h) T) =
      kottwitzBasis n L (hodgeDegrees h) T := by
  have hbase : CMPerm.base G τ0 = τ0 := by
    rw [CMPerm.base_apply, CMPerm.baseFun, hfix]
  have hcross : CMPerm.crosses G τ0 = false := by
    rw [CMPerm.crosses, hfix]
    rfl
  have hsymm : (CMPerm.base G).symm τ0 = τ0 := by
    rw [Equiv.symm_apply_eq, hbase]
  rw [kottwitzBasis, Basis.piTensorProduct_apply, frobOp_tprod]
  congr 1
  funext τ'
  by_cases hτ' : τ' = τ0
  · subst hτ'
    unfold factorEquiv
    split_ifs with hc
    · rw [hsymm, hcross] at hc
      exact absurd hc Bool.false_ne_true
    apply Subtype.ext
    rw [LinearEquiv.coe_ofEq_apply]
    exact exteriorPower_basisFun_coe_congr T hsymm
  · have hσ : (CMPerm.base G).symm τ' ≠ τ0 := by
      intro e
      apply hτ'
      rw [← hbase, ← e, Equiv.apply_symm_apply]
    rw [exteriorPower_basisFun_eq_hwVector (hodge_false_le h hsum _) (hτ0 _ hσ),
      factorEquiv_hwVector,
      exteriorPower_basisFun_eq_hwVector (hodge_false_le h hsum _) (hτ0 _ hτ')]

variable (G : CMPerm S) (f : ℕ)
  (hGf : ∀ x, h (((G ^ f : CMPerm S) : Equiv.Perm (S × Bool)) x) = h x)

/-- `V(Φ_v)` acts on the standard basis vector `⨂_τ e_{T_τ}` by the scalar
`s^{f · dim} · ⟨N(t̂), wt(T)⟩`. -/
theorem kottwitzFrobenius_torusElement_basis {τ0 : S}
    (hτ0 : ∀ τ, τ ≠ τ0 → h (τ, false) = 0 ∨ h (τ, false) = n)
    (hfix : ((G ^ f : CMPerm S) : Equiv.Perm (S × Bool)) (τ0, true) = (τ0, true))
    (s : Lˣ) (t : Lˣ × (S → Fin n → Lˣ)) (T : ∀ τ, Set.powersetCard (Fin n) (hodgeDegrees h τ)) :
    kottwitzFrobenius h hsum G f hGf s (torusElement t) (kottwitzBasis n L (hodgeDegrees h) T) =
      ((s : L) ^ (f * hodgeDim h) * (cocharPairing t (normCochar n G f (basisWeight T)) : L)) •
        kottwitzBasis n L (hodgeDegrees h) T := by
  rw [kottwitzFrobenius_eq, LinearMap.smul_apply, frobeniusElement, map_mul,
    LinearEquiv.coe_toLinearMap, LinearEquiv.mul_apply, kottwitzRep_frob,
    frobOp_kottwitzBasis h hsum (G ^ f) hGf hτ0 hfix, kottwitzRep_inl, frobNorm_torusElement,
    dualRep_torusElement_basis, cocharPairing_torusNorm, smul_smul]

theorem toMatrix_eq_diagonal {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    [Module L M] (b : Module.Basis ι L M) (φ : M →ₗ[L] M) (d : ι → L)
    (hφ : ∀ i, φ (b i) = d i • b i) :
    LinearMap.toMatrix b b φ = Matrix.diagonal d := by
  ext i j
  rw [LinearMap.toMatrix_apply, hφ, map_smul, Basis.repr_self, Finsupp.smul_apply,
    Matrix.diagonal_apply, Finsupp.single_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

theorem charpoly_toMatrix_eq_prod {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    [Module L M] (b : Module.Basis ι L M) (φ : M →ₗ[L] M) (d : ι → L)
    (hφ : ∀ i, φ (b i) = d i • b i) :
    (LinearMap.toMatrix b b φ).charpoly = ∏ i, (X - C (d i)) := by
  rw [toMatrix_eq_diagonal b φ d hφ, Matrix.charpoly_diagonal]

/-- For Harris's signature, Kottwitz's polynomial of a torus element is the product of
`X - s^{f · dim} ⟨N(t̂), wt(T)⟩` over the standard basis of `W`. -/
theorem kottwitzCharpoly_torusElement [DecidableEq S] {τ0 : S}
    (hτ0 : ∀ τ, τ ≠ τ0 → h (τ, false) = 0 ∨ h (τ, false) = n)
    (hfix : ((G ^ f : CMPerm S) : Equiv.Perm (S × Bool)) (τ0, true) = (τ0, true))
    (s : Lˣ) (t : Lˣ × (S → Fin n → Lˣ)) :
    kottwitzCharpoly h hsum G f hGf s (torusElement t) =
      ∏ T : (∀ τ, Set.powersetCard (Fin n) (hodgeDegrees h τ)),
        (X - C ((s : L) ^ (f * hodgeDim h) *
          (cocharPairing t (normCochar n G f (basisWeight T)) : L))) := by
  have key := charpoly_toMatrix_eq_prod (kottwitzBasis n L (hodgeDegrees h))
    (kottwitzFrobenius h hsum G f hGf s (torusElement t))
    (fun T => (s : L) ^ (f * hodgeDim h) *
      (cocharPairing t (normCochar n G f (basisWeight T)) : L))
    (kottwitzFrobenius_torusElement_basis h hsum G f hGf hτ0 hfix s t)
  unfold kottwitzCharpoly
  convert key

end Frobenius

/-! ### The pairing with `2ρ` is Frobenius-invariant -/

section TwoRho

variable {S : Type u} [Fintype S] {n : ℕ}

theorem rho_coeff_rev (k : Fin n) :
    ((n : ℤ) - 1 - 2 * ((Fin.rev k : ℕ) : ℤ)) = -((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ)) := by
  rw [Fin.val_rev]
  have := k.isLt
  omega

theorem sum_rho_coeff : ∑ k : Fin n, ((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ)) = 0 := by
  have h := Fintype.sum_equiv Fin.revPerm (fun k : Fin n => ((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ)))
    (fun k => -((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ))) (fun k => by
      rw [Fin.revPerm_apply, rho_coeff_rev, neg_neg])
  rw [Finset.sum_neg_distrib] at h
  omega

theorem twoRhoPairing_cocharPullback (G : CMPerm S) (a : ℤ × (S → Fin n → ℤ)) :
    twoRhoPairing (cocharPullback n G a) = twoRhoPairing a := by
  rw [cocharPullback_apply, twoRhoPairing, twoRhoPairing]
  refine Fintype.sum_equiv (CMPerm.base G) _ _ fun τ => ?_
  by_cases hc : CMPerm.crosses G τ = true
  · simp only [hc, ite_true]
    have e : ∑ k : Fin n, ((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ)) * a.2 (CMPerm.base G τ) (Fin.rev k) =
        -∑ k : Fin n, ((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ)) * a.2 (CMPerm.base G τ) k := by
      rw [← Finset.sum_neg_distrib]
      exact Fintype.sum_equiv Fin.revPerm _ _ fun k => by
        rw [Fin.revPerm_apply, rho_coeff_rev, neg_mul, neg_neg]
    rw [Finset.sum_congr rfl (fun k _ => mul_sub _ _ _), Finset.sum_sub_distrib,
      ← Finset.sum_mul, sum_rho_coeff, zero_mul, zero_sub, e, neg_neg]
  · rw [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, ite_false]

theorem twoRhoPairing_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ × (S → Fin n → ℤ)) :
    twoRhoPairing (∑ i ∈ s, a i) = ∑ i ∈ s, twoRhoPairing (a i) :=
  map_sum (AddMonoidHom.mk' twoRhoPairing twoRhoPairing_add) a s

theorem twoRhoPairing_normCochar (G : CMPerm S) (f : ℕ) (a : ℤ × (S → Fin n → ℤ)) :
    twoRhoPairing (normCochar n G f a) = f * twoRhoPairing a := by
  rw [normCochar, twoRhoPairing_sum]
  simp [twoRhoPairing_cocharPullback]

omit [Fintype S] in
theorem normCochar_add (G : CMPerm S) (f : ℕ) (a b : ℤ × (S → Fin n → ℤ)) :
    normCochar n G f (a + b) = normCochar n G f a + normCochar n G f b := by
  simp only [normCochar, map_add, Finset.sum_add_distrib]

variable [DecidableEq S]

theorem twoRhoPairing_posCochar (τ0 : S) (j : Fin n) :
    twoRhoPairing (posCochar τ0 j) = (n : ℤ) - 1 - 2 * ((j : ℕ) : ℤ) := by
  rw [twoRhoPairing, Finset.sum_eq_single τ0
    (fun τ _ hτ => by simp [posCochar, Pi.single_eq_of_ne hτ]) (by simp)]
  simp [posCochar, Pi.single_apply]

end TwoRho

/-! ### Reduction to the index `j` at `τ₀` -/

section Harris

variable {L : Type v} [Field L] {n : ℕ} {S : Type u} [Fintype S] [DecidableEq S]
variable {h : S × Bool → ℕ} {τ0 : S}

omit [Fintype S] [DecidableEq S] in
theorem card_harris (h0 : h (τ0, false) = 1)
    (T : ∀ τ, Set.powersetCard (Fin n) (hodgeDegrees h τ)) : (T τ0).1.card = 1 :=
  (Set.powersetCard.card_eq (T τ0)).trans h0

/-- The index `j` with `T_{τ₀} = {j}`, for `k_{τ₀} = 1`. -/
def harrisIndex (h0 : h (τ0, false) = 1) (T : ∀ τ, Set.powersetCard (Fin n) (hodgeDegrees h τ)) :
    Fin n :=
  (T τ0).1.min' (Finset.card_pos.mp (by rw [card_harris h0 T]; exact one_pos))

omit [Fintype S] [DecidableEq S] in
theorem harrisIndex_spec (h0 : h (τ0, false) = 1)
    (T : ∀ τ, Set.powersetCard (Fin n) (hodgeDegrees h τ)) :
    (T τ0).1 = {harrisIndex h0 T} := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (card_harris h0 T)
  have hm : harrisIndex h0 T ∈ (T τ0).1 := Finset.min'_mem _ _
  rw [ha, Finset.mem_singleton] at hm
  rw [ha, hm]

omit [Fintype S] [DecidableEq S] in
theorem mem_harris_ne (hτ0 : ∀ τ, τ ≠ τ0 → h (τ, false) = 0 ∨ h (τ, false) = n)
    (T : ∀ τ, Set.powersetCard (Fin n) (hodgeDegrees h τ)) {τ : S} (hτ : τ ≠ τ0) (j : Fin n) :
    j ∈ (T τ).1 ↔ h (τ, false) ≠ 0 := by
  have hc := Set.powersetCard.card_eq (T τ)
  rcases hτ0 τ hτ with hz | hn
  · have : (T τ).1 = ∅ := Finset.card_eq_zero.mp (hc.trans hz)
    simp [this, hz]
  · have : (T τ).1 = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Fintype.card_fin]; exact hc.trans hn)
    have hpos := j.pos
    rw [this]
    simp only [Finset.mem_univ, true_iff]
    omega

variable (h τ0) in
/-- The weight common to all basis vectors for Harris's signature: `a₀ = -1`, and
`a_{τ,i} = -1` if `τ = τ₀` or `k_τ = 0`, `0` otherwise. -/
def harrisBaseWeight : ℤ × (S → Fin n → ℤ) :=
  (-1, fun τ _ => if τ = τ0 then -1 else if h (τ, false) = 0 then -1 else 0)

omit [Fintype S] in
theorem basisWeight_eq_harris (h0 : h (τ0, false) = 1)
    (hτ0 : ∀ τ, τ ≠ τ0 → h (τ, false) = 0 ∨ h (τ, false) = n)
    (T : ∀ τ, Set.powersetCard (Fin n) (hodgeDegrees h τ)) :
    basisWeight T = harrisBaseWeight (n := n) h τ0 + posCochar τ0 (harrisIndex h0 T) := by
  refine Prod.ext ?_ ?_
  · simp [basisWeight, harrisBaseWeight, posCochar]
  · funext τ j
    by_cases hτ : τ = τ0
    · subst hτ
      simp only [basisWeight, harrisBaseWeight, posCochar, harrisIndex_spec h0 T,
        Finset.mem_singleton, Prod.snd_add, Pi.add_apply, ite_true, Pi.single_eq_same,
        Pi.single_apply]
      split_ifs <;> norm_num
    · simp only [basisWeight, harrisBaseWeight, posCochar, mem_harris_ne hτ0 T hτ j,
        Prod.snd_add, Pi.add_apply, hτ, ite_false, Pi.single_eq_of_ne hτ, Pi.zero_apply]
      split_ifs <;> simp_all

omit [Fintype S] in
theorem harrisIndex_injective (h0 : h (τ0, false) = 1)
    (hτ0 : ∀ τ, τ ≠ τ0 → h (τ, false) = 0 ∨ h (τ, false) = n) :
    Function.Injective (harrisIndex (n := n) h0) := by
  intro T T' e
  funext τ
  apply Subtype.ext
  by_cases hτ : τ = τ0
  · subst hτ
    rw [harrisIndex_spec h0 T, harrisIndex_spec h0 T', e]
  · ext j
    rw [mem_harris_ne hτ0 T hτ, mem_harris_ne hτ0 T' hτ]

theorem harrisIndex_bijective (h0 : h (τ0, false) = 1)
    (hτ0 : ∀ τ, τ ≠ τ0 → h (τ, false) = 0 ∨ h (τ, false) = n) :
    Function.Bijective (harrisIndex (n := n) h0) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨harrisIndex_injective h0 hτ0, ?_⟩
  rw [card_kottwitzBasisIndex, kottwitzDim, Finset.prod_eq_single τ0, Fintype.card_fin]
  · simp [hodgeDegrees, h0]
  · intro τ _ hτ
    rcases hτ0 τ hτ with hz | hn
    · simp [hodgeDegrees, hz]
    · simp [hodgeDegrees, hn]
  · simp

variable (h) (hsum : ∀ τ, h (τ, true) + h (τ, false) = n) (G : CMPerm S) (f : ℕ)
  (hGf : ∀ x, h (((G ^ f : CMPerm S) : Equiv.Perm (S × Bool)) x) = h x)

/-- Kottwitz's polynomial for Harris's signature `k_{τ₀} = 1`, `k_τ ∈ {0, n}` otherwise, when
the Frobenius power `G^f` fixes `(τ₀, true)`:
`P = ∏_j (X - s^{f · dim} ⟨N(t̂), a₀⟩ ⟨N(t̂), e_{τ₀,j}⟩)`. -/
theorem kottwitzCharpoly_harris (h0 : h (τ0, false) = 1)
    (hτ0 : ∀ τ, τ ≠ τ0 → h (τ, false) = 0 ∨ h (τ, false) = n)
    (hfix : ((G ^ f : CMPerm S) : Equiv.Perm (S × Bool)) (τ0, true) = (τ0, true))
    (s : Lˣ) (t : Lˣ × (S → Fin n → Lˣ)) :
    kottwitzCharpoly h hsum G f hGf s (torusElement t) =
      ∏ j : Fin n, (X - C ((s : L) ^ (f * hodgeDim h) *
        (cocharPairing t (normCochar n G f (harrisBaseWeight h τ0)) : L) *
        (cocharPairing t (normCochar n G f (posCochar τ0 j)) : L))) := by
  rw [kottwitzCharpoly_torusElement h hsum G f hGf hτ0 hfix s t]
  refine Fintype.prod_bijective (harrisIndex h0) (harrisIndex_bijective h0 hτ0) _ _ fun T => ?_
  rw [basisWeight_eq_harris h0 hτ0 T, normCochar_add, cocharPairing_add, Units.val_mul, mul_assoc]

end Harris

/-! ### Counting returns to a periodic point -/

section Orbits

open Function

/-- For a `P`-periodic `g`, `∑_{r < N P} g r = N • ∑_{r < P} g r`. -/
theorem sum_range_mul_of_periodic {M : Type*} [AddCommMonoid M] {g : ℕ → M} {P : ℕ}
    (hg : Periodic g P) (N : ℕ) :
    ∑ r ∈ Finset.range (N * P), g r = N • ∑ r ∈ Finset.range P, g r := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [add_comm]
    exact hg.nat_mul N r

/-- Exactly one `r < P` has `P ∣ r + r₀`. -/
theorem sum_range_ite_dvd_add {P : ℕ} (hP : 0 < P) (r0 : ℕ) :
    ∑ r ∈ Finset.range P, (if P ∣ r + r0 then (1 : ℤ) else 0) = 1 := by
  have hle : r0 ≤ P * r0 := Nat.le_mul_of_pos_left r0 hP
  have h1 : P ∣ (P * r0 - r0) % P + r0 := by
    have e : (P * r0 - r0) % P + r0 ≡ (P * r0 - r0) + r0 [MOD P] :=
      Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
    rw [Nat.sub_add_cancel hle] at e
    exact (Nat.modEq_zero_iff_dvd).mp (e.trans ((Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right P r0)))
  rw [Finset.sum_eq_single ((P * r0 - r0) % P)]
  · rw [ite_eq_left_iff.mpr fun h => absurd h1 h]
  · intro r hr hne
    refine ite_eq_right_iff.mpr fun hd => (hne ?_).elim
    have e : r ≡ (P * r0 - r0) % P [MOD P] := Nat.ModEq.add_right_cancel' r0
      (((Nat.modEq_zero_iff_dvd).mpr hd).trans ((Nat.modEq_zero_iff_dvd).mpr h1).symm)
    exact e.eq_of_lt_of_lt (Finset.mem_range.mp hr) (Nat.mod_lt _ hP)
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.mod_lt _ hP)) h

open Classical in
/-- If `x₀` has minimal period `P > 0` under the permutation `F`, then among `r < N P`
exactly `N` satisfy `Fʳ x = x₀` when `x` lies in the forward orbit of `x₀`, and none
otherwise. -/
theorem sum_range_ite_pow_apply_eq {α : Type*} (F : Equiv.Perm α) {x0 : α}
    (hpos : 0 < minimalPeriod F x0) (N : ℕ) (x : α) :
    ∑ r ∈ Finset.range (N * minimalPeriod F x0), (if (F ^ r) x = x0 then (1 : ℤ) else 0) =
      if ∃ r : ℕ, (F ^ r) x0 = x then (N : ℤ) else 0 := by
  split_ifs with hx
  · obtain ⟨r0, rfl⟩ := hx
    have key : ∀ r, (F ^ r) ((F ^ r0) x0) = x0 ↔ minimalPeriod F x0 ∣ r + r0 := by
      intro r
      rw [← Equiv.Perm.mul_apply, ← pow_add, ← isPeriodicPt_iff_minimalPeriod_dvd, IsPeriodicPt,
        IsFixedPt, Equiv.Perm.coe_pow]
    simp_rw [key]
    rw [sum_range_mul_of_periodic (fun r => ?_) N, sum_range_ite_dvd_add hpos, nsmul_eq_mul,
      mul_one]
    rw [show r + minimalPeriod F x0 + r0 = r + r0 + minimalPeriod F x0 by ring]
    simp only [Nat.dvd_add_self_right]
  · refine Finset.sum_eq_zero fun r _ => ite_eq_right_iff.mpr fun h => (hx ?_).elim
    have hper : IsPeriodicPt F (minimalPeriod F x0 * r) x0 :=
      (isPeriodicPt_minimalPeriod F x0).mul_const r
    have hle : r ≤ minimalPeriod F x0 * r := Nat.le_mul_of_pos_left r hpos
    refine ⟨minimalPeriod F x0 * r - r, ?_⟩
    apply (F ^ r).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hle, h, Equiv.Perm.coe_pow]
    exact hper.eq

end Orbits

/-! ### The norm of a position cocharacter -/

section PositionNorm

variable {S : Type u} [Fintype S] [DecidableEq S] {n : ℕ}

omit [Fintype S] in
/-- The coordinates of the pullback of `e_{τ₀,j}` along a CM permutation. -/
theorem cocharPullback_posCochar_snd (G : CMPerm S) (τ0 : S) (j : Fin n) (τ : S) (k : Fin n) :
    (cocharPullback n G (posCochar τ0 j)).2 τ k =
      (if (G : Equiv.Perm (S × Bool)) (τ, true) = (τ0, true) ∧ k = j then 1 else 0) -
        (if (G : Equiv.Perm (S × Bool)) (τ, true) = (τ0, false) ∧ Fin.rev k = j then 1 else 0) := by
  have key : ∀ y : S × Bool,
      (if (!y.2) = true then (0 : ℤ) - (Pi.single τ0 (Pi.single j 1) : S → Fin n → ℤ) y.1 k.rev
        else (Pi.single τ0 (Pi.single j 1) : S → Fin n → ℤ) y.1 k) =
      (if y = (τ0, true) ∧ k = j then 1 else 0) - if y = (τ0, false) ∧ k.rev = j then 1 else 0 := by
    rintro ⟨τ', b⟩
    by_cases hτ : τ' = τ0
    · subst hτ
      cases b <;> simp [Pi.single_apply, eq_comm]
    · cases b <;> simp [hτ]
  rw [cocharPullback_apply]
  simp only [CMPerm.crosses, CMPerm.base_apply, CMPerm.baseFun, posCochar]
  exact key _

omit [Fintype S] in
theorem normCochar_posCochar_fst (G : CMPerm S) (f : ℕ) (τ0 : S) (j : Fin n) :
    (normCochar n G f (posCochar τ0 j)).1 = 0 := by
  rw [normCochar, Prod.fst_sum]
  exact Finset.sum_eq_zero fun r _ => rfl

omit [Fintype S] in
theorem normCochar_posCochar_snd (G : CMPerm S) (f : ℕ) (τ0 : S) (j : Fin n) (τ : S)
    (k : Fin n) :
    (normCochar n G f (posCochar τ0 j)).2 τ k =
      ∑ r ∈ Finset.range f,
        ((if ((G ^ r : CMPerm S) : Equiv.Perm (S × Bool)) (τ, true) = (τ0, true) ∧ k = j
            then 1 else 0) -
          (if ((G ^ r : CMPerm S) : Equiv.Perm (S × Bool)) (τ, true) = (τ0, false) ∧
            Fin.rev k = j then 1 else 0)) := by
  rw [normCochar, Prod.snd_sum, Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun r _ => cocharPullback_posCochar_snd _ _ _ _ _

end PositionNorm

/-! ### Frobenius orbits and places above `p` -/

section Places

open NumberField IsDedekindDomain KottwitzUnramified Langlands.Global.AdelicFunctoriality Function

variable {K : Type v} [Field K] [NumberField K]

omit [NumberField K] in
/-- A power of a permutation commuting with complex conjugation commutes with it. -/
private theorem pow_apply_conjugate_aux (F : Equiv.Perm (K →+* ℂ))
    (hF : ∀ i, F (ComplexEmbedding.conjugate i) = ComplexEmbedding.conjugate (F i)) (r : ℕ)
    (i : K →+* ℂ) :
    (F ^ r) (ComplexEmbedding.conjugate i) = ComplexEmbedding.conjugate ((F ^ r) i) := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih => rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, hF]

open Classical in
/-- Counting the returns of the Frobenius orbit of an embedding `i` to `i₀` in `f` steps,
when the orbit of `i₀` has length `f_w` and consists of the embeddings inducing the place
`w` of `i₀`. -/
theorem sum_range_frobeniusPerm_pow_eq {p : ℕ} [Fact p.Prime] (θ : ℂ →+* PadicAlgCl p)
    {i0 : K →+* ℂ} {f : ℕ} (hf : (frobeniusPerm K p θ ^ f) i0 = i0)
    (hper : minimalPeriod (frobeniusPerm K p θ) i0 = inertiaDegree (harrisPlace p θ i0))
    (horb : ∀ j : K →+* ℂ, harrisPlace p θ j = harrisPlace p θ i0 ↔
      ∃ r : ℕ, (frobeniusPerm K p θ ^ r) i0 = j)
    (hfpos : 0 < f) (i : K →+* ℂ) :
    ∑ r ∈ Finset.range f, (if (frobeniusPerm K p θ ^ r) i = i0 then (1 : ℤ) else 0) =
      if harrisPlace p θ i = harrisPlace p θ i0 then
        ((f / inertiaDegree (harrisPlace p θ i0) : ℕ) : ℤ) else 0 := by
  classical
  have hpt : IsPeriodicPt (frobeniusPerm K p θ) f i0 := by
    rw [IsPeriodicPt, IsFixedPt, ← Equiv.Perm.coe_pow]
    exact hf
  have hdvd := hpt.minimalPeriod_dvd
  have hpos := hpt.minimalPeriod_pos hfpos
  have hrange : Finset.range f = Finset.range (f / minimalPeriod (frobeniusPerm K p θ) i0 *
      minimalPeriod (frobeniusPerm K p θ) i0) := by
    rw [Nat.div_mul_cancel hdvd]
  rw [hrange, sum_range_ite_pow_apply_eq _ hpos, hper]
  simp only [horb]

variable {E : Type u} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [IsTotallyComplex K] [Algebra E K] [Algebra.IsQuadraticExtension E K]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {σ : SecondKindInvolution E K A} {n : ℕ} {p : ℕ} [Fact p.Prime]

variable {Φ : (E →+* ℝ) → (K →+* ℂ)} (hΦ : IsCMSection E K Φ) (θ : ℂ →+* PadicAlgCl p)

/-- The Frobenius CM permutation moves the index `x` to `y` exactly when the Frobenius
permutation of the complex embeddings moves the corresponding embeddings. -/
theorem frobeniusCMPerm_pow_apply_eq_iff (r : ℕ) (x y : (E →+* ℝ) × Bool) :
    ((frobeniusCMPerm hΦ θ ^ r : CMPerm (E →+* ℝ)) : Equiv.Perm _) x = y ↔
      (frobeniusPerm K p θ ^ r) (cmFactorEmbedding Φ x) = cmFactorEmbedding Φ y := by
  rw [frobeniusCMPerm, ofEmbeddingPerm_pow_apply, Equiv.symm_apply_eq]
  rfl

include hΦ in
/-- For Harris's signature with `n ≥ 3`, the Frobenius power `F^{f}` (`f` the local degree
of the reflex field) fixes the embedding `Φ τ₀`. -/
theorem frobeniusPerm_pow_localDegree_harris (hn : 3 ≤ n) (nfun : (K →+* ℂ) → ℕ)
    (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n) {τ0 : E →+* ℝ}
    (h0 : nfun (ComplexEmbedding.conjugate (Φ τ0)) = 1)
    (hτ0 : ∀ τ, τ ≠ τ0 → nfun (ComplexEmbedding.conjugate (Φ τ)) = 0 ∨
      nfun (ComplexEmbedding.conjugate (Φ τ)) = n) :
    (frobeniusPerm K p θ ^ localDegree p θ nfun) (Φ τ0) = Φ τ0 := by
  have key : ∀ x : (E →+* ℝ) × Bool, nfun (cmFactorEmbedding Φ x) = 1 → x = (τ0, false) := by
    rintro ⟨τ, b⟩ hx
    have hc := hconj (Φ τ)
    by_cases hτ : τ = τ0
    · subst hτ
      cases b
      · rfl
      · simp only [cmFactorEmbedding, ite_true] at hx
        omega
    · exfalso
      rcases hτ0 τ hτ with h | h <;> cases b <;>
        simp only [cmFactorEmbedding, ite_true, Bool.false_eq_true, ite_false] at hx <;> omega
  have hy : nfun ((frobeniusPerm K p θ ^ localDegree p θ nfun)
      (ComplexEmbedding.conjugate (Φ τ0))) = 1 := by
    exact (hodgeOrbitDegree_preserves (frobeniusPerm K p θ) nfun _).trans h0
  have hx := key ((cmFactorEmbeddingEquiv Φ hΦ).symm
    ((frobeniusPerm K p θ ^ localDegree p θ nfun) (ComplexEmbedding.conjugate (Φ τ0))))
    (by rw [← cmFactorEmbeddingEquiv_apply Φ hΦ, Equiv.apply_symm_apply]; exact hy)
  rw [Equiv.symm_apply_eq, cmFactorEmbeddingEquiv_apply,
    pow_apply_conjugate_aux _ (frobeniusPerm_conjugate (E := E) (K := K) (p := p) θ)] at hx
  have hx' : ComplexEmbedding.conjugate ((frobeniusPerm K p θ ^ localDegree p θ nfun) (Φ τ0)) =
      ComplexEmbedding.conjugate (Φ τ0) := by
    rw [hx]
    simp [cmFactorEmbedding]
  exact (ComplexEmbedding.involutive_conjugate K).injective hx'

variable {τ0 : E →+* ℝ}

/-- Under the orbit hypotheses, the Frobenius norm of the position cocharacter `e_{τ₀,j}` is
the rational cocharacter `(f / f_w) λ_{w,j}` of the place `w` of `Φ τ₀`. -/
theorem normCochar_posCochar_eq_embeddingCochar [DecidableEq (E →+* ℝ)] {f : ℕ}
    (hf : (frobeniusPerm K p θ ^ f) (Φ τ0) = Φ τ0)
    (hper : minimalPeriod (frobeniusPerm K p θ) (Φ τ0) = inertiaDegree (harrisPlace p θ (Φ τ0)))
    (horb : ∀ j : K →+* ℂ, harrisPlace p θ j = harrisPlace p θ (Φ τ0) ↔
      ∃ r : ℕ, (frobeniusPerm K p θ ^ r) (Φ τ0) = j)
    (hfpos : 0 < f) (j : Fin n) :
    normCochar n (frobeniusCMPerm hΦ θ) f (posCochar τ0 j) =
      embeddingCochar θ Φ ((f / inertiaDegree (harrisPlace p θ (Φ τ0))) •
        positionCocharacter E (rationalPrimePlace p) n (harrisPlace p θ (Φ τ0)) j) := by
  classical
  set w := harrisPlace p θ (Φ τ0) with hw
  set N := f / inertiaDegree w with hN
  have hcount := sum_range_frobeniusPerm_pow_eq θ hf hper horb hfpos
  have h1 : ∀ τ, ∑ r ∈ Finset.range f, (if ((frobeniusCMPerm hΦ θ ^ r : CMPerm (E →+* ℝ)) :
      Equiv.Perm _) (τ, true) = (τ0, true) then (1 : ℤ) else 0) =
      if harrisPlace p θ (Φ τ) = w then (N : ℤ) else 0 := by
    intro τ
    rw [← hcount (Φ τ)]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [frobeniusCMPerm_pow_apply_eq_iff, cmFactorEmbedding, ite_true]
  have h2 : ∀ τ, ∑ r ∈ Finset.range f, (if ((frobeniusCMPerm hΦ θ ^ r : CMPerm (E →+* ℝ)) :
      Equiv.Perm _) (τ, true) = (τ0, false) then (1 : ℤ) else 0) =
      if harrisPlace p θ (Φ τ) = placeConj (E := E) (rationalPrimePlace p) w then (N : ℤ)
        else 0 := by
    intro τ
    have e : harrisPlace p θ (Φ τ) = placeConj (E := E) (rationalPrimePlace p) w ↔
        harrisPlace p θ (ComplexEmbedding.conjugate (Φ τ)) = w := by
      rw [harrisPlace_conjugate (E := E)]
      constructor
      · intro h
        rw [h, placeConj_placeConj]
      · intro h
        rw [← h, placeConj_placeConj]
    simp only [e]
    rw [← hcount (ComplexEmbedding.conjugate (Φ τ))]
    refine Finset.sum_congr rfl fun r _ => ?_
    have e' : (frobeniusPerm K p θ ^ r) (Φ τ) = ComplexEmbedding.conjugate (Φ τ0) ↔
        (frobeniusPerm K p θ ^ r) (ComplexEmbedding.conjugate (Φ τ)) = Φ τ0 := by
      rw [pow_apply_conjugate_aux _ (frobeniusPerm_conjugate (E := E) (K := K) (p := p) θ)]
      exact ⟨fun h => by rw [h, ComplexEmbedding.involutive_conjugate K],
        fun h => by rw [← h, ComplexEmbedding.involutive_conjugate K]⟩
    simp only [frobeniusCMPerm_pow_apply_eq_iff, cmFactorEmbedding, ite_true,
      Bool.false_eq_true, ite_false, e']
  refine Prod.ext ?_ (funext fun τ => funext fun k => ?_)
  · rw [normCochar_posCochar_fst]
    simp [embeddingCochar, positionCocharacter]
  · rw [normCochar_posCochar_snd, Finset.sum_sub_distrib]
    have e1 : ∀ r, (if ((frobeniusCMPerm hΦ θ ^ r : CMPerm (E →+* ℝ)) : Equiv.Perm _) (τ, true) =
          (τ0, true) ∧ k = j then (1 : ℤ) else 0) =
        if k = j then (if ((frobeniusCMPerm hΦ θ ^ r : CMPerm (E →+* ℝ)) : Equiv.Perm _)
          (τ, true) = (τ0, true) then 1 else 0) else 0 := fun r => by
      by_cases hk : k = j <;> simp [hk]
    have e2 : ∀ r, (if ((frobeniusCMPerm hΦ θ ^ r : CMPerm (E →+* ℝ)) : Equiv.Perm _) (τ, true) =
          (τ0, false) ∧ Fin.rev k = j then (1 : ℤ) else 0) =
        if Fin.rev k = j then (if ((frobeniusCMPerm hΦ θ ^ r : CMPerm (E →+* ℝ)) :
          Equiv.Perm _) (τ, true) = (τ0, false) then 1 else 0) else 0 := fun r => by
      by_cases hk : Fin.rev k = j <;> simp [hk]
    rw [Finset.sum_congr rfl fun r _ => e1 r, Finset.sum_congr rfl fun r _ => e2 r,
      Finset.sum_ite_irrel, Finset.sum_ite_irrel, Finset.sum_const_zero, h1, h2]
    have hrev : k = Fin.rev j ↔ Fin.rev k = j :=
      ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
    simp only [embeddingCochar]
    rw [AddSubgroup.coe_nsmul, Prod.smul_fst, Pi.smul_apply, Pi.smul_apply,
      positionCocharacter_coord]
    simp only [ite_and, hrev]
    split_ifs <;> simp

variable (c : UnramifiedChart σ (rationalPrimePlace p) n)

/-- Under the orbit hypotheses, a normalized lift pairs with the Frobenius norm of
`e_{τ₀,j}` to the `(f / f_w)`-th power of the normalized position value at `(w, j)`. -/
theorem cocharPairing_normCochar_posCochar_harris [DecidableEq (E →+* ℝ)] {Ω : Type uΩ}
    [Field Ω] (s : SqrtPrime (rationalPrimePlace p) Ω) (ξ : c.torus →* Ωˣ)
    (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) (ht : IsNormalizedLift c θ (Φ := Φ) s ξ t) {f : ℕ}
    (hf : (frobeniusPerm K p θ ^ f) (Φ τ0) = Φ τ0)
    (hper : minimalPeriod (frobeniusPerm K p θ) (Φ τ0) = inertiaDegree (harrisPlace p θ (Φ τ0)))
    (horb : ∀ j : K →+* ℂ, harrisPlace p θ j = harrisPlace p θ (Φ τ0) ↔
      ∃ r : ℕ, (frobeniusPerm K p θ ^ r) (Φ τ0) = j)
    (hfpos : 0 < f) (j : Fin n) :
    cocharPairing t (normCochar n (frobeniusCMPerm hΦ θ) f (posCochar τ0 j)) =
      c.positionValue s ξ (harrisPlace p θ (Φ τ0)) j ^
        (f / inertiaDegree (harrisPlace p θ (Φ τ0))) := by
  have key := normCochar_posCochar_eq_embeddingCochar hΦ θ hf hper horb hfpos j
  have h2 : twoRhoPairing (embeddingCochar θ Φ ((f / inertiaDegree (harrisPlace p θ (Φ τ0))) •
      positionCocharacter E (rationalPrimePlace p) n (harrisPlace p θ (Φ τ0)) j)) =
      (f : ℤ) * ((n : ℤ) - 1 - 2 * ((j : ℕ) : ℤ)) := by
    rw [← key, twoRhoPairing_normCochar, twoRhoPairing_posCochar]
  have hdvd : inertiaDegree (harrisPlace p θ (Φ τ0)) ∣ f := by
    rw [← hper]
    apply IsPeriodicPt.minimalPeriod_dvd
    rw [IsPeriodicPt, IsFixedPt, ← Equiv.Perm.coe_pow]
    exact hf
  have e : (((f / inertiaDegree (harrisPlace p θ (Φ τ0)) : ℕ) : ℤ) *
      (inertiaDegree (harrisPlace p θ (Φ τ0)) : ℤ)) = f := by
    exact_mod_cast Nat.div_mul_cancel hdvd
  rw [key, ht, h2, UnramifiedChart.positionValue, mul_pow, ofAdd_nsmul, map_pow, map_pow]
  congr 1
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  rw [← e]
  ring

/-- **Kottwitz's polynomial for Harris's signature.** For `n ≥ 3`, `k_{τ₀} = 1` and
`k_τ ∈ {0, n}` at the other real places, and under the orbit hypotheses at `Φ τ₀`
(the Frobenius orbit of `Φ τ₀` has length `f_w` and consists of the embeddings inducing the
place `w` of `Φ τ₀`), `P(π_p, E_v) = ∏_j (X - α β_j^{f / f_w})`, where
`β_j = positionValue s ξ w j` are the base-change parameters at `w`, `f` is the local degree
of the reflex field, and `α = s^{f · dim} ⟨N(t̂), a₀⟩`. -/
theorem kottwitzPolynomialOf_harris [DecidableEq (E →+* ℝ)] (hn : 3 ≤ n)
    (nfun : (K →+* ℂ) → ℕ) (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n)
    (h0 : nfun (ComplexEmbedding.conjugate (Φ τ0)) = 1)
    (hτ0 : ∀ τ, τ ≠ τ0 → nfun (ComplexEmbedding.conjugate (Φ τ)) = 0 ∨
      nfun (ComplexEmbedding.conjugate (Φ τ)) = n)
    (hper : minimalPeriod (frobeniusPerm K p θ) (Φ τ0) = inertiaDegree (harrisPlace p θ (Φ τ0)))
    (horb : ∀ j : K →+* ℂ, harrisPlace p θ j = harrisPlace p θ (Φ τ0) ↔
      ∃ r : ℕ, (frobeniusPerm K p θ ^ r) (Φ τ0) = j)
    {Ω : Type uΩ} [Field Ω] (s : SqrtPrime (rationalPrimePlace p) Ω) (ξ : c.torus →* Ωˣ)
    (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) (ht : IsNormalizedLift c θ (Φ := Φ) s ξ t) :
    kottwitzPolynomialOf θ hΦ nfun hconj s.1 t =
      ∏ j : Fin n, (X - C (((s.1 : Ω) ^ (localDegree p θ nfun * hodgeDim (cmHodge hΦ nfun)) *
        (cocharPairing t (normCochar n (frobeniusCMPerm hΦ θ) (localDegree p θ nfun)
          (harrisBaseWeight (cmHodge hΦ nfun) τ0)) : Ω)) *
        ((c.positionValue s ξ (harrisPlace p θ (Φ τ0)) j ^
          (localDegree p θ nfun / inertiaDegree (harrisPlace p θ (Φ τ0))) : Ωˣ) : Ω))) := by
  have hf := frobeniusPerm_pow_localDegree_harris hΦ θ hn nfun hconj h0 hτ0
  have h0' : cmHodge hΦ nfun (τ0, false) = 1 := by
    rw [cmHodge, cmFactorEmbeddingEquiv_apply]
    exact h0
  have hτ0' : ∀ τ, τ ≠ τ0 → cmHodge hΦ nfun (τ, false) = 0 ∨ cmHodge hΦ nfun (τ, false) = n := by
    intro τ hτ
    rw [cmHodge, cmFactorEmbeddingEquiv_apply]
    exact hτ0 τ hτ
  have hfix : ((frobeniusCMPerm hΦ θ ^ localDegree p θ nfun : CMPerm (E →+* ℝ)) :
      Equiv.Perm _) (τ0, true) = (τ0, true) := by
    rw [frobeniusCMPerm_pow_apply_eq_iff]
    exact hf
  unfold kottwitzPolynomialOf
  rw [kottwitzCharpoly_harris (cmHodge hΦ nfun) (cmHodge_add hΦ nfun hconj) (frobeniusCMPerm hΦ θ)
    (localDegree p θ nfun) (cmHodge_frobenius_pow θ hΦ nfun) h0' hτ0' hfix]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [cocharPairing_normCochar_posCochar_harris hΦ θ c s ξ t ht hf hper horb
    (hodgeOrbitDegree_pos _ _) j]

/-- The same identity through the base-change parameter of item 4: `P(π_p, E_v)` is the
product of `X - α β^{f / f_w}` over the multiset `BC(π)_w` of base-change Satake parameters at
the place `w` of `Φ τ₀`. -/
theorem kottwitzPolynomialOf_harris_baseChangeParameter [DecidableEq (E →+* ℝ)] (hn : 3 ≤ n)
    (nfun : (K →+* ℂ) → ℕ) (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n)
    (h0 : nfun (ComplexEmbedding.conjugate (Φ τ0)) = 1)
    (hτ0 : ∀ τ, τ ≠ τ0 → nfun (ComplexEmbedding.conjugate (Φ τ)) = 0 ∨
      nfun (ComplexEmbedding.conjugate (Φ τ)) = n)
    (hper : minimalPeriod (frobeniusPerm K p θ) (Φ τ0) = inertiaDegree (harrisPlace p θ (Φ τ0)))
    (horb : ∀ j : K →+* ℂ, harrisPlace p θ j = harrisPlace p θ (Φ τ0) ↔
      ∃ r : ℕ, (frobeniusPerm K p θ ^ r) (Φ τ0) = j)
    {Ω : Type uΩ} [Field Ω] (s : SqrtPrime (rationalPrimePlace p) Ω) (ξ : c.torus →* Ωˣ)
    (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) (ht : IsNormalizedLift c θ (Φ := Φ) s ξ t) :
    kottwitzPolynomialOf θ hΦ nfun hconj s.1 t =
      (((c.baseChangeParameter s ξ (harrisPlace p θ (Φ τ0)) : Sym Ωˣ n) : Multiset Ωˣ).map
        fun β => X - C (((s.1 : Ω) ^ (localDegree p θ nfun * hodgeDim (cmHodge hΦ nfun)) *
          (cocharPairing t (normCochar n (frobeniusCMPerm hΦ θ) (localDegree p θ nfun)
            (harrisBaseWeight (cmHodge hΦ nfun) τ0)) : Ω)) *
          ((β ^ (localDegree p θ nfun / inertiaDegree (harrisPlace p θ (Φ τ0))) : Ωˣ) : Ω))).prod := by
  rw [kottwitzPolynomialOf_harris hΦ θ c hn nfun hconj h0 hτ0 hper horb s ξ t ht,
    UnramifiedChart.baseChangeParameter, symOfFn]
  change _ = (Multiset.map _ ((List.ofFn _ : List Ωˣ) : Multiset Ωˣ)).prod
  rw [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
  rfl

include hΦ in
/-- **When `f = f_w`.** In addition to the hypotheses of `kottwitzPolynomialOf_harris`, assume
that every Frobenius power fixing `Φ τ₀` preserves Kottwitz's function (`hR`; this holds when
the reflex field of the CM type lies in the image of `K` under `Φ τ₀`, see the Markdown).
Then the local degree of the reflex field is the inertia degree of the place `w` of `Φ τ₀`. -/
theorem localDegree_eq_inertiaDegree_harris (hn : 3 ≤ n)
    (nfun : (K →+* ℂ) → ℕ) (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n)
    (h0 : nfun (ComplexEmbedding.conjugate (Φ τ0)) = 1)
    (hτ0 : ∀ τ, τ ≠ τ0 → nfun (ComplexEmbedding.conjugate (Φ τ)) = 0 ∨
      nfun (ComplexEmbedding.conjugate (Φ τ)) = n)
    (hper : minimalPeriod (frobeniusPerm K p θ) (Φ τ0) = inertiaDegree (harrisPlace p θ (Φ τ0)))
    (hR : ∀ r : ℕ, (frobeniusPerm K p θ ^ r) (Φ τ0) = Φ τ0 →
      ∀ i, nfun ((frobeniusPerm K p θ ^ r) i) = nfun i) :
    localDegree p θ nfun = inertiaDegree (harrisPlace p θ (Φ τ0)) := by
  have hf := frobeniusPerm_pow_localDegree_harris hΦ θ hn nfun hconj h0 hτ0
  have hpt : IsPeriodicPt (frobeniusPerm K p θ) (localDegree p θ nfun) (Φ τ0) := by
    rw [IsPeriodicPt, IsFixedPt, ← Equiv.Perm.coe_pow]
    exact hf
  have hfpos : 0 < localDegree p θ nfun := hodgeOrbitDegree_pos _ _
  have hdvd := hpt.minimalPeriod_dvd
  have hmpos := hpt.minimalPeriod_pos hfpos
  have hfix : (frobeniusPerm K p θ ^ minimalPeriod (frobeniusPerm K p θ) (Φ τ0)) (Φ τ0) =
      Φ τ0 := by
    rw [Equiv.Perm.coe_pow]
    exact iterate_minimalPeriod
  have hle : localDegree p θ nfun ≤ minimalPeriod (frobeniusPerm K p θ) (Φ τ0) :=
    Nat.find_min' _ ⟨hmpos, hR _ hfix⟩
  rw [← hper]
  exact le_antisymm hle (Nat.le_of_dvd hfpos hdvd)

/-- **Exponent one.** Under the additional hypothesis `hR` of
`localDegree_eq_inertiaDegree_harris`, `P(π_p, E_v)` is the product of `X - α β` over the
base-change parameter `BC(π)_w` of item 4 at the place `w` of `Φ τ₀`. -/
theorem kottwitzPolynomialOf_harris_baseChangeParameter_of_preserves [DecidableEq (E →+* ℝ)]
    (hn : 3 ≤ n)
    (nfun : (K →+* ℂ) → ℕ) (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n)
    (h0 : nfun (ComplexEmbedding.conjugate (Φ τ0)) = 1)
    (hτ0 : ∀ τ, τ ≠ τ0 → nfun (ComplexEmbedding.conjugate (Φ τ)) = 0 ∨
      nfun (ComplexEmbedding.conjugate (Φ τ)) = n)
    (hper : minimalPeriod (frobeniusPerm K p θ) (Φ τ0) = inertiaDegree (harrisPlace p θ (Φ τ0)))
    (horb : ∀ j : K →+* ℂ, harrisPlace p θ j = harrisPlace p θ (Φ τ0) ↔
      ∃ r : ℕ, (frobeniusPerm K p θ ^ r) (Φ τ0) = j)
    (hR : ∀ r : ℕ, (frobeniusPerm K p θ ^ r) (Φ τ0) = Φ τ0 →
      ∀ i, nfun ((frobeniusPerm K p θ ^ r) i) = nfun i)
    {Ω : Type uΩ} [Field Ω] (s : SqrtPrime (rationalPrimePlace p) Ω) (ξ : c.torus →* Ωˣ)
    (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) (ht : IsNormalizedLift c θ (Φ := Φ) s ξ t) :
    kottwitzPolynomialOf θ hΦ nfun hconj s.1 t =
      (((c.baseChangeParameter s ξ (harrisPlace p θ (Φ τ0)) : Sym Ωˣ n) : Multiset Ωˣ).map
        fun β : Ωˣ => X - C (((s.1 : Ω) ^ (localDegree p θ nfun * hodgeDim (cmHodge hΦ nfun)) *
          (cocharPairing t (normCochar n (frobeniusCMPerm hΦ θ) (localDegree p θ nfun)
            (harrisBaseWeight (cmHodge hΦ nfun) τ0)) : Ω)) * (β : Ω))).prod := by
  have heq := localDegree_eq_inertiaDegree_harris hΦ θ hn nfun hconj h0 hτ0 hper hR
  have hone : localDegree p θ nfun / inertiaDegree (harrisPlace p θ (Φ τ0)) = 1 := by
    rw [← heq]
    exact Nat.div_self (hodgeOrbitDegree_pos _ _)
  rw [kottwitzPolynomialOf_harris_baseChangeParameter hΦ θ c hn nfun hconj h0 hτ0 hper horb
    s ξ t ht]
  simp only [hone, pow_one]

/-! ### The Library's Harris datum -/

variable (H : HarrisSignatureCharts σ n Φ)

open Classical in
omit [NumberField E] [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A]
  [IsScalarTower ℚ K A] in
include hΦ in
/-- Kottwitz's function of Harris's datum at the CM type: `n - 1` at the distinguished real
place and `n` elsewhere. -/
theorem harrisCharts_hodgeFunction_section (τ : E →+* ℝ) :
    H.hodgeFunction (Φ τ) = if τ = H.distinguished then n - 1 else n := by
  rw [H.hodgeFunction_apply, realPlaceBelow_of_isCMSection E hΦ, ite_eq_left rfl]

open Classical in
omit [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A] in
include hΦ in
/-- Kottwitz's function of Harris's datum at the conjugates of the CM type: `1` at the
distinguished real place and `0` elsewhere. -/
theorem harrisCharts_hodgeFunction_conjugate_section (τ : E →+* ℝ) :
    H.hodgeFunction (ComplexEmbedding.conjugate (Φ τ)) =
      if τ = H.distinguished then 1 else 0 := by
  have hne : ComplexEmbedding.conjugate (Φ τ) ≠ Φ τ := by
    intro e
    have := (cmFactorEmbeddingEquiv Φ hΦ).injective (a₁ := (τ, false)) (a₂ := (τ, true))
      (by simp only [cmFactorEmbeddingEquiv_apply, cmFactorEmbedding, Bool.false_eq_true,
        ite_false, ite_true, e])
    simp at this
  rw [H.hodgeFunction_apply, realPlaceBelow_conjugate, realPlaceBelow_of_isCMSection E hΦ,
    ite_eq_right hne]

omit [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A] in
include hΦ in
/-- Kottwitz's function of Harris's datum satisfies `n(i) + n(ī) = n`. -/
theorem harrisCharts_hodgeFunction_add_conjugate (i : K →+* ℂ) :
    H.hodgeFunction i + H.hodgeFunction (ComplexEmbedding.conjugate i) = n := by
  have hn := H.rank_gt_one
  obtain ⟨⟨τ, b⟩, rfl⟩ := (cmFactorEmbeddingEquiv Φ hΦ).surjective i
  rw [cmFactorEmbeddingEquiv_apply]
  cases b
  · simp only [cmFactorEmbedding, Bool.false_eq_true, ite_false,
      (ComplexEmbedding.involutive_conjugate K) (Φ τ)]
    rw [harrisCharts_hodgeFunction_conjugate_section hΦ H,
      harrisCharts_hodgeFunction_section hΦ H]
    split_ifs <;> omega
  · simp only [cmFactorEmbedding, ite_true]
    rw [harrisCharts_hodgeFunction_conjugate_section hΦ H,
      harrisCharts_hodgeFunction_section hΦ H]
    split_ifs <;> omega

/-- **Kottwitz's polynomial for the Library's Harris datum.** For Harris's signature charts
`H` (signature `(n - 1, 1)` at the distinguished real place `τ₁`, `(n, 0)` elsewhere) with
`n ≥ 3`, Kottwitz's function `H.hodgeFunction`, and under the orbit hypotheses at `Φ τ₁`,
`P(π_p, E_v)` is the product of `X - α β^{f / f_w}` over the base-change parameter `BC(π)_w`
of item 4 at the place `w` of `Φ τ₁`. -/
theorem kottwitzPolynomialOf_harrisCharts [DecidableEq (E →+* ℝ)] (hn : 3 ≤ n)
    (hper : minimalPeriod (frobeniusPerm K p θ) (Φ H.distinguished) =
      inertiaDegree (harrisPlace p θ (Φ H.distinguished)))
    (horb : ∀ j : K →+* ℂ, harrisPlace p θ j = harrisPlace p θ (Φ H.distinguished) ↔
      ∃ r : ℕ, (frobeniusPerm K p θ ^ r) (Φ H.distinguished) = j)
    {Ω : Type uΩ} [Field Ω] (s : SqrtPrime (rationalPrimePlace p) Ω) (ξ : c.torus →* Ωˣ)
    (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) (ht : IsNormalizedLift c θ (Φ := Φ) s ξ t) :
    kottwitzPolynomialOf θ hΦ H.hodgeFunction (harrisCharts_hodgeFunction_add_conjugate hΦ H)
        s.1 t =
      (((c.baseChangeParameter s ξ (harrisPlace p θ (Φ H.distinguished)) : Sym Ωˣ n) :
          Multiset Ωˣ).map
        fun β => X - C (((s.1 : Ω) ^
            (localDegree p θ H.hodgeFunction * hodgeDim (cmHodge hΦ H.hodgeFunction)) *
          (cocharPairing t (normCochar n (frobeniusCMPerm hΦ θ) (localDegree p θ H.hodgeFunction)
            (harrisBaseWeight (cmHodge hΦ H.hodgeFunction) H.distinguished)) : Ω)) *
          ((β ^ (localDegree p θ H.hodgeFunction /
            inertiaDegree (harrisPlace p θ (Φ H.distinguished))) : Ωˣ) : Ω))).prod := by
  refine kottwitzPolynomialOf_harris_baseChangeParameter hΦ θ c hn H.hodgeFunction
    (harrisCharts_hodgeFunction_add_conjugate hΦ H) ?_ ?_ hper horb s ξ t ht
  · rw [harrisCharts_hodgeFunction_conjugate_section hΦ H, ite_eq_left rfl]
  · intro τ hτ
    left
    rw [harrisCharts_hodgeFunction_conjugate_section hΦ H, ite_eq_right hτ]

end Places

end Langlands.Shimura.KottwitzDual
