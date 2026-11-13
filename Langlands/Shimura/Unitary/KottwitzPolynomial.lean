import Langlands.Shimura.Unitary.KottwitzRepresentation
import Langlands.Shimura.Unitary.KottwitzPrincipalSeries
import Langlands.Shimura.Unitary.HarrisCMTypePlaces
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Kottwitz's unramified representation `V(π_p, E_v)` and polynomial `P(π_p, E_v)`

For an unramified parameter `φ(Frob) = t̂ ⋊ Frob` of the unitary similitude group,
`V(Φ_v) = Z(Φ_v) · r(φ(Φ_v))` with `φ(Φ_v) = N_f(t̂) ⋊ Φ_v`, `Φ_v = Frob^f`,
`Z(Φ_v) = (√p)^{f · dim S}`, and `P` is the characteristic polynomial of `V(Φ_v)`.
See the paired Markdown for conventions and sources.
-/

noncomputable section

open NumberField

namespace Langlands.Shimura.KottwitzDual

universe u v w uL uV uΩ

/-! ### The dual torus and its pairing with cocharacters -/

section DualTorus

variable {S : Type u} [Fintype S] {n : ℕ} {L : Type v} [Field L]

/-- The element `(ζ, (diag s_τ)_τ)` of the diagonal torus of `Ĝ`. -/
def torusElement (t : Lˣ × (S → Fin n → Lˣ)) : DualGroup S n L :=
  (t.1, fun τ => diagUnit (t.2 τ))

theorem diagUnit_mul {n : ℕ} (s s' : Fin n → Lˣ) :
    diagUnit (s * s') = diagUnit (L := L) s * diagUnit s' := by
  ext : 1
  simp [diagUnit_val, Matrix.diagonal_mul_diagonal]

omit [Fintype S] in
theorem torusElement_mul (t t' : Lˣ × (S → Fin n → Lˣ)) :
    torusElement (t * t') = torusElement t * torusElement t' := by
  ext1
  · rfl
  · funext τ
    exact diagUnit_mul _ _

/-- The pairing `λ(t̂) = ζ^{a₀} ∏_{τ,k} s_{τ,k}^{a_{τ,k}}` of the dual torus with a
cocharacter in its free coordinates `(a₀, (a_{τ,k}))`. -/
def cocharPairing (t : Lˣ × (S → Fin n → Lˣ)) (a : ℤ × (S → Fin n → ℤ)) : Lˣ :=
  t.1 ^ a.1 * ∏ τ, ∏ k, t.2 τ k ^ a.2 τ k

/-- `⟨2ρ, λ⟩ = Σ_τ Σ_k (n - 1 - 2k) a_{τ,k}` for the upper triangular Borel subgroup. -/
def twoRhoPairing (a : ℤ × (S → Fin n → ℤ)) : ℤ :=
  ∑ τ, ∑ k : Fin n, ((n : ℤ) - 1 - 2 * (k : ℤ)) * a.2 τ k

theorem cocharPairing_mul (t t' : Lˣ × (S → Fin n → Lˣ)) (a : ℤ × (S → Fin n → ℤ)) :
    cocharPairing (t * t') a = cocharPairing t a * cocharPairing t' a := by
  simp only [cocharPairing, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_zpow,
    Finset.prod_mul_distrib]
  ac_rfl

variable (S n L) in
/-- `ε̂ = (2ρ)(-1)`: the central element `(1, ((-1)^{n-1})_τ)` of `Ĝ`. -/
def epsilonHat : Lˣ × (S → Fin n → Lˣ) := (1, fun _ _ => (-1) ^ (n - 1))

theorem neg_one_zpow_rho (n : ℕ) (k : Fin n) (z : ℤ) :
    ((-1 : Lˣ) ^ (n - 1)) ^ z = (-1) ^ (((n : ℤ) - 1 - 2 * (k : ℤ)) * z) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact k.elim0
  have h1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [← zpow_natCast, ← zpow_mul, h1, show ((n : ℤ) - 1 - 2 * (k : ℤ)) * z =
    ((n : ℤ) - 1) * z + 2 * (-(k : ℤ) * z) by ring, zpow_add, zpow_mul (-1) 2]
  simp

theorem units_zpow_sum {ι : Type*} (a : Lˣ) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ i ∈ s, e i) = ∏ i ∈ s, a ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem cocharPairing_epsilonHat (a : ℤ × (S → Fin n → ℤ)) :
    cocharPairing (epsilonHat S n L) a = (-1) ^ twoRhoPairing a := by
  simp only [cocharPairing, epsilonHat, one_zpow, one_mul, twoRhoPairing, units_zpow_sum]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun k _ => ?_
  exact neg_one_zpow_rho n k _

end DualTorus

/-! ### The norm map and the restriction of a parameter -/

section Norm

variable {S : Type u} [Fintype S] {n : ℕ} {L : Type v} [Field L] (G : CMPerm S)

/-- The norm `N_f(x) = x · σ(x) ⋯ σ^{f-1}(x)` for the action `σ` of `G` on `Ĝ`. -/
def frobNorm (x : DualGroup S n L) : ℕ → DualGroup S n L
  | 0 => 1
  | f + 1 => frobNorm x f * (dualAction S n L G ^ f) x

theorem frobNorm_zero (x : DualGroup S n L) : frobNorm G x 0 = 1 := rfl

theorem frobNorm_succ (x : DualGroup S n L) (f : ℕ) :
    frobNorm G x (f + 1) = frobNorm G x f * (dualAction S n L G ^ f) x := rfl

/-- `Φ^f (x ⋊ 1) = (σ^f(x) ⋊ 1) Φ^f` in `Ĝ ⋊ ℤ`. -/
theorem frob_pow_mul_inl (f : ℕ) (x : DualGroup S n L) :
    LGroup.frob (n := n) (L := L) G ^ f * SemidirectProduct.inl x =
      SemidirectProduct.inl ((dualAction S n L G ^ f) x) * LGroup.frob G ^ f := by
  rw [LGroup.frob, ← map_pow]
  have key : (zpowersHom (MulAut (DualGroup S n L)) (dualAction S n L G))
      (Multiplicative.ofAdd 1 ^ f) x = (dualAction S n L G ^ f) x := by
    simp [zpowersHom_apply]
  rw [← key, SemidirectProduct.inl_aut, map_inv SemidirectProduct.inr, inv_mul_cancel_right]

/-- `(x ⋊ Φ)^f = N_f(x) ⋊ Φ^f` in `Ĝ ⋊ ℤ`. -/
theorem inl_mul_frob_pow (x : DualGroup S n L) (f : ℕ) :
    (SemidirectProduct.inl x * LGroup.frob G) ^ f =
      SemidirectProduct.inl (frobNorm G x f) * LGroup.frob (n := n) (L := L) G ^ f := by
  induction f with
  | zero => simp [frobNorm_zero]
  | succ f ih =>
    rw [pow_succ, ih, frobNorm_succ, map_mul, pow_succ, mul_assoc, ← mul_assoc (_ ^ f),
      frob_pow_mul_inl]
    simp only [mul_assoc]

/-- The inclusion of `^L(G_{E_v})` sends `N_f(x) ⋊ Φ_v` to `(x ⋊ Φ)^f`: this element is
the restriction of the parameter `φ` to `W_{E_v}`, evaluated at `Φ_v`. -/
theorem restrictionHom_frob (f : ℕ) :
    LGroup.restrictionHom G f (LGroup.frob (n := n) (L := L) (G ^ f)) =
      LGroup.frob G ^ f := by
  simp only [LGroup.restrictionHom, LGroup.frob, SemidirectProduct.lift_inr,
    MonoidHom.comp_apply]
  rw [← map_pow]
  congr 1
  apply Multiplicative.toAdd.injective
  simp [zpowersHom_apply]

theorem restrictionHom_inl (f : ℕ) (a : DualGroup S n L) :
    LGroup.restrictionHom G f (SemidirectProduct.inl a) = SemidirectProduct.inl a :=
  SemidirectProduct.lift_inl _ _ _ _

theorem restrictionHom_frobNorm (x : DualGroup S n L) (f : ℕ) :
    LGroup.restrictionHom G f
        (SemidirectProduct.inl (frobNorm G x f) * LGroup.frob (n := n) (L := L) (G ^ f)) =
      (SemidirectProduct.inl x * LGroup.frob G) ^ f := by
  rw [inl_mul_frob_pow, map_mul, restrictionHom_inl, restrictionHom_frob]

/-- Twisted conjugation: `N_f(y x σ(y)⁻¹) = y N_f(x) σ^f(y)⁻¹`. -/
theorem frobNorm_twistedConj (x y : DualGroup S n L) (f : ℕ) :
    frobNorm G (y * x * ((dualAction S n L G) y)⁻¹) f =
      y * frobNorm G x f * ((dualAction S n L G ^ f) y)⁻¹ := by
  induction f with
  | zero => simp [frobNorm_zero]
  | succ f ih =>
    rw [frobNorm_succ, frobNorm_succ, ih, map_mul, map_mul, map_inv, pow_succ,
      MulAut.mul_apply]
    group

end Norm

/-! ### `V(Φ_v)` and its characteristic polynomial -/

section Polynomial

variable {S : Type u} [Fintype S] {n : ℕ} {L : Type v} [Field L]
variable (h : S × Bool → ℕ) (hsum : ∀ τ, h (τ, true) + h (τ, false) = n)
  (G : CMPerm S) (f : ℕ) (hGf : ∀ x, h (((G ^ f : CMPerm S) : Equiv.Perm (S × Bool)) x) = h x)

/-- `dim S_K = Σ_τ n(Φτ) (n - n(Φτ))`, the pairing `⟨2ρ, μ⟩`. -/
def hodgeDim (h : S × Bool → ℕ) : ℕ := ∑ τ, h (τ, true) * h (τ, false)

/-- The element `φ(Φ_v) = N_f(x) ⋊ Φ_v` of `^L(G_{E_v}) = Ĝ ⋊ ⟨Φ_v⟩`. -/
def frobeniusElement (x : DualGroup S n L) : LGroup S n L (G ^ f) :=
  SemidirectProduct.inl (frobNorm G x f) * LGroup.frob (G ^ f)

/-- Kottwitz's unramified representation `V = (r ∘ φ_{E_v}) ⊗ Z` of the unramified
quotient `ℤ` of `W_{E_v}`, whose generator is geometric Frobenius `Φ_v`:
`Φ_v ↦ Z(Φ_v) · r(N_f(x) ⋊ Φ_v)` with `Z(Φ_v) = s^{f · dim S}`. -/
def kottwitzV (s : Lˣ) (x : DualGroup S n L) :
    Multiplicative ℤ →* (KottwitzSpace S n L (hodgeDegrees h) ≃ₗ[L]
      KottwitzSpace S n L (hodgeDegrees h)) :=
  zpowersHom _ ((LinearEquiv.smulOfUnit (s ^ (f * hodgeDim h))).trans
    (kottwitzRep h hsum (G ^ f) hGf (frobeniusElement G f x)))

/-- `V(Φ_v)` as an endomorphism of `W`. -/
def kottwitzFrobenius (s : Lˣ) (x : DualGroup S n L) :
    Module.End L (KottwitzSpace S n L (hodgeDegrees h)) :=
  (kottwitzV h hsum G f hGf s x (Multiplicative.ofAdd 1)).toLinearMap

theorem kottwitzFrobenius_eq (s : Lˣ) (x : DualGroup S n L) :
    kottwitzFrobenius h hsum G f hGf s x =
      ((s : L) ^ (f * hodgeDim h)) •
        (kottwitzRep h hsum (G ^ f) hGf (frobeniusElement G f x)).toLinearMap := by
  refine LinearMap.ext fun y => ?_
  simp only [kottwitzFrobenius, kottwitzV, zpowersHom_apply, toAdd_ofAdd, zpow_one]
  change kottwitzRep h hsum (G ^ f) hGf (frobeniusElement G f x)
    ((s ^ (f * hodgeDim h)) • y) = _
  rw [Units.smul_def, map_smul, Units.val_pow_eq_pow_val]
  rfl

variable (n L) in
/-- The standard basis `⨂_τ e_{T_τ}` of `W = ⨂_τ ⋀^{k τ} Lⁿ`, indexed by families of
subsets `T_τ ⊂ {0, …, n-1}` of size `k τ`. -/
def kottwitzBasis (k : S → ℕ) :
    Module.Basis (∀ τ, Set.powersetCard (Fin n) (k τ)) L (KottwitzSpace S n L k) :=
  Basis.piTensorProduct fun τ => (Pi.basisFun L (Fin n)).exteriorPower (k τ)

/-- `dim r = ∏_τ C(n, n - n(Φτ))`. -/
def kottwitzDim (n : ℕ) (k : S → ℕ) : ℕ := ∏ τ, n.choose (k τ)

theorem card_kottwitzBasisIndex (k : S → ℕ) [DecidableEq S] :
    Fintype.card (∀ τ, Set.powersetCard (Fin n) (k τ)) = kottwitzDim n k := by
  rw [Fintype.card_pi, kottwitzDim]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
    Fintype.card_fin]

open scoped Classical in
/-- Kottwitz's polynomial `P = det(X - V(Φ_v))`, computed in the standard basis of `W`. -/
def kottwitzCharpoly (s : Lˣ) (x : DualGroup S n L) : Polynomial L :=
  (LinearMap.toMatrix (kottwitzBasis n L (hodgeDegrees h)) (kottwitzBasis n L (hodgeDegrees h))
    (kottwitzFrobenius h hsum G f hGf s x)).charpoly

/-- `P` is monic. -/
theorem kottwitzCharpoly_monic (s : Lˣ) (x : DualGroup S n L) :
    (kottwitzCharpoly h hsum G f hGf s x).Monic := by
  classical
  unfold kottwitzCharpoly
  exact Matrix.charpoly_monic _

/-- `P` has degree `dim r = ∏_τ C(n, n - n(Φτ))`. -/
theorem kottwitzCharpoly_natDegree (s : Lˣ) (x : DualGroup S n L) :
    (kottwitzCharpoly h hsum G f hGf s x).natDegree = kottwitzDim n (hodgeDegrees h) := by
  classical
  rw [kottwitzCharpoly, Matrix.charpoly_natDegree_eq_dim]
  convert card_kottwitzBasisIndex (n := n) (hodgeDegrees h)

/-- The characteristic polynomial in the standard basis is invariant under conjugation. -/
theorem charpoly_toMatrix_conj {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*}
    [AddCommMonoid W] [Module L W] (B : Module.Basis ι L W) (R : W ≃ₗ[L] W)
    (φ : Module.End L W) :
    (LinearMap.toMatrix B B (R.toLinearMap ∘ₗ φ ∘ₗ R.symm.toLinearMap)).charpoly =
      (LinearMap.toMatrix B B φ).charpoly := by
  rw [LinearMap.toMatrix_comp B B B, LinearMap.toMatrix_comp B B B, Matrix.charpoly_mul_comm,
    mul_assoc, ← LinearMap.toMatrix_comp B B B,
    show R.symm.toLinearMap ∘ₗ R.toLinearMap = LinearMap.id from
      LinearMap.ext R.symm_apply_apply, LinearMap.toMatrix_id, mul_one]

/-- `P` only depends on the twisted conjugacy class of `x`. -/
theorem kottwitzCharpoly_twistedConj (s : Lˣ) (x y : DualGroup S n L) :
    kottwitzCharpoly h hsum G f hGf s (y * x * ((dualAction S n L G) y)⁻¹) =
      kottwitzCharpoly h hsum G f hGf s x := by
  classical
  have hconj : frobeniusElement G f (y * x * ((dualAction S n L G) y)⁻¹) =
      SemidirectProduct.inl y * frobeniusElement G f x * (SemidirectProduct.inl y)⁻¹ := by
    rw [frobeniusElement, frobeniusElement, frobNorm_twistedConj]
    have hfrob : LGroup.frob (n := n) (L := L) (G ^ f) * (SemidirectProduct.inl y)⁻¹ =
        SemidirectProduct.inl ((dualAction S n L G ^ f) y)⁻¹ * LGroup.frob (G ^ f) := by
      have h1 := frob_pow_mul_inl (G ^ f) 1 y⁻¹
      simp only [pow_one] at h1
      rw [← map_pow (dualAction S n L) G f, ← map_inv, h1, map_inv]
    rw [map_mul, map_mul, mul_assoc (SemidirectProduct.inl y * _), ← hfrob]
    group
  set R := kottwitzRep h hsum (G ^ f) hGf (SemidirectProduct.inl y)
  have hV : kottwitzFrobenius h hsum G f hGf s (y * x * ((dualAction S n L G) y)⁻¹) =
      R.toLinearMap ∘ₗ kottwitzFrobenius h hsum G f hGf s x ∘ₗ R.symm.toLinearMap := by
    rw [kottwitzFrobenius_eq, kottwitzFrobenius_eq, hconj, map_mul, map_mul, map_inv]
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply,
      LinearMap.comp_apply, map_smul]
    rfl
  rw [kottwitzCharpoly, kottwitzCharpoly, hV, charpoly_toMatrix_conj]

end Polynomial

/-! ### Changing the square root of `p` -/

section Sign

variable {S : Type u} [Fintype S] {n : ℕ} {L : Type v} [Field L]

theorem diagUnit_const_val (c : Lˣ) :
    ((diagUnit (fun _ : Fin n => c) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (c : L) • (1 : Matrix (Fin n) (Fin n) L) := by
  rw [diagUnit_val]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem diagUnit_const_commute (c : Lˣ) (g : GL (Fin n) L) :
    diagUnit (fun _ => c) * g = g * diagUnit (fun _ => c) := by
  ext : 1
  simp only [Units.val_mul, diagUnit_const_val, Matrix.smul_mul, Matrix.mul_smul, one_mul,
    mul_one]

theorem twist_diagUnit_const (c : Lˣ) (hc : c * c = 1) :
    twist n L (diagUnit (fun _ => c)) = diagUnit (fun _ => c) := by
  have hinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  ext : 1
  rw [twist_apply, Units.val_mul, Units.val_mul, transposeInv_val]
  have h1 : ((diagUnit (fun _ : Fin n => c))⁻¹ : GL (Fin n) L).val =
      (c : L) • (1 : Matrix (Fin n) (Fin n) L) := by
    rw [← diagUnit_const_val]
    change Matrix.diagonal (fun _ => ((c⁻¹ : Lˣ) : L)) = _
    rw [hinv]
    rfl
  rw [h1, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, mul_one, Matrix.smul_mul,
    Units.mul_inv, diagUnit_const_val]

/-- The sign `(-1)^{n-1}` squares to one. -/
theorem neg_one_pow_pred_mul_self (n : ℕ) : ((-1 : Lˣ) ^ (n - 1)) * (-1) ^ (n - 1) = 1 := by
  rw [← mul_pow]
  simp

theorem neg_one_pow_pred_pow_self (n : ℕ) : (((-1 : Lˣ) ^ (n - 1) : Lˣ) : L) ^ n = 1 := by
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← pow_mul]
  exact Even.neg_one_pow (by rw [mul_comm]; exact Nat.even_mul_pred_self n)

variable (S n L) in
/-- The central element `ε̂ ∈ Ĝ`. -/
abbrev epsilonElement : DualGroup S n L := torusElement (epsilonHat S n L)

omit [Fintype S] in
theorem epsilonElement_commute (y : DualGroup S n L) :
    epsilonElement S n L * y = y * epsilonElement S n L := by
  ext1
  · simp [epsilonElement, torusElement, epsilonHat]
  · funext τ
    exact diagUnit_const_commute _ _

theorem dualAction_epsilonElement (G : CMPerm S) :
    dualAction S n L G (epsilonElement S n L) = epsilonElement S n L := by
  rw [dualAction_apply]
  ext1
  · rw [dualEndo_fst]
    have hdet : Matrix.GeneralLinearGroup.det
        (diagUnit (fun _ : Fin n => ((-1 : Lˣ) ^ (n - 1)))) = 1 := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, diagUnit_const_val, Matrix.det_smul,
        Matrix.det_one, mul_one, Fintype.card_fin, neg_one_pow_pred_pow_self, Units.val_one]
    simp [epsilonElement, torusElement, epsilonHat, hdet]
  · funext τ'
    rw [dualEndo_snd]
    split_ifs
    · exact twist_diagUnit_const _ (neg_one_pow_pred_mul_self n)
    · rfl

theorem dualAction_pow_epsilonElement (G : CMPerm S) (j : ℕ) :
    (dualAction S n L G ^ j) (epsilonElement S n L) = epsilonElement S n L := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, MulAut.mul_apply, dualAction_epsilonElement, ih]

theorem frobNorm_mul_epsilonElement (G : CMPerm S) (x : DualGroup S n L) (f : ℕ) :
    frobNorm G (x * epsilonElement S n L) f = frobNorm G x f * epsilonElement S n L ^ f := by
  induction f with
  | zero => simp [frobNorm_zero]
  | succ f ih =>
    rw [frobNorm_succ, frobNorm_succ, ih, map_mul, dualAction_pow_epsilonElement, pow_succ]
    have hc : epsilonElement S n L ^ f * (dualAction S n L G ^ f) x =
        (dualAction S n L G ^ f) x * epsilonElement S n L ^ f :=
      (Commute.pow_left (epsilonElement_commute _) f).eq
    rw [mul_assoc (frobNorm G x f), ← mul_assoc (epsilonElement S n L ^ f), hc]
    simp only [mul_assoc]

theorem frobeniusElement_mul_epsilonElement (G : CMPerm S) (f : ℕ) (x : DualGroup S n L) :
    frobeniusElement G f (x * epsilonElement S n L) =
      SemidirectProduct.inl (epsilonElement S n L ^ f) * frobeniusElement G f x := by
  rw [frobeniusElement, frobeniusElement, frobNorm_mul_epsilonElement,
    (Commute.pow_left (epsilonElement_commute (frobNorm G x f)) f).symm.eq, map_mul,
    mul_assoc]

theorem map_toLin'_smul_one (a : L) (k : ℕ) (y : ⋀[L]^k (Fin n → L)) :
    exteriorPower.map k (Matrix.toLin' (a • (1 : Matrix (Fin n) (Fin n) L))) y = a ^ k • y := by
  have hmap : exteriorPower.map k (Matrix.toLin' (a • (1 : Matrix (Fin n) (Fin n) L))) =
      a ^ k • LinearMap.id := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
    simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
      LinearMap.smul_apply, LinearMap.id_apply]
    have hv : (Matrix.toLin' (a • (1 : Matrix (Fin n) (Fin n) L)) ∘ v) = fun i => a • v i := by
      funext i
      simp
    rw [hv, AlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hmap]
  rfl

theorem wedgeRep_epsilon (k : ℕ) (y : ⋀[L]^k (Fin n → L)) :
    wedgeRep k (diagUnit (fun _ : Fin n => ((-1 : Lˣ) ^ (n - 1)))) y =
      (((-1 : Lˣ) ^ (n - 1) : Lˣ) : L) ^ k • y := by
  rw [wedgeRep_apply, diagUnit_const_val, map_toLin'_smul_one, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin, neg_one_pow_pred_pow_self, inv_one, one_smul]

theorem dualRep_epsilonElement (k : S → ℕ) (y : KottwitzSpace S n L k) :
    dualRep k (epsilonElement S n L) y =
      (∏ τ, (((-1 : Lˣ) ^ (n - 1) : Lˣ) : L) ^ k τ) • y := by
  have hlin : (dualRep k (epsilonElement S n L)).toLinearMap =
      (∏ τ, (((-1 : Lˣ) ^ (n - 1) : Lˣ) : L) ^ k τ) • LinearMap.id := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe, dualRep_tprod,
      LinearMap.smul_apply, LinearMap.id_apply]
    simp only [epsilonElement, torusElement, epsilonHat, Units.val_one, inv_one, one_smul,
      wedgeRep_epsilon]
    rw [MultilinearMap.map_smul_univ]
  exact LinearMap.congr_fun hlin y

theorem even_hodge (m k : ℕ) : Even (m * k + (m + k - 1) * k) := by
  rcases k with _ | j
  · simp
  · have h : m * (j + 1) + (m + (j + 1) - 1) * (j + 1) = 2 * (m * (j + 1)) + j * (j + 1) := by
      rw [show m + (j + 1) - 1 = m + j by omega]
      ring
    rw [h]
    exact (even_two_mul _).add (Nat.even_mul_succ_self j)

variable (h : S × Bool → ℕ) (hsum : ∀ τ, h (τ, true) + h (τ, false) = n)
  (G : CMPerm S) (f : ℕ) (hGf : ∀ x, h (((G ^ f : CMPerm S) : Equiv.Perm (S × Bool)) x) = h x)

include hsum in
theorem sign_cancel :
    (-1 : L) ^ (f * hodgeDim h) *
      (∏ τ, (((-1 : Lˣ) ^ (n - 1) : Lˣ) : L) ^ h (τ, false)) ^ f = 1 := by
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, ← pow_add]
  apply Even.neg_one_pow
  rw [mul_comm f, ← add_mul]
  apply Even.mul_right
  rw [hodgeDim, ← Finset.sum_add_distrib]
  refine Finset.even_sum _ fun τ _ => ?_
  rw [← hsum τ]
  exact even_hodge _ _

/-- Replacing `√p` by `-√p` and `x` by `x ε̂` does not change `V(Φ_v)`. -/
theorem kottwitzFrobenius_neg (s : Lˣ) (x : DualGroup S n L) :
    kottwitzFrobenius h hsum G f hGf (-s) (x * epsilonElement S n L) =
      kottwitzFrobenius h hsum G f hGf s x := by
  have hinl : kottwitzRep h hsum (G ^ f) hGf
      (SemidirectProduct.inl (epsilonElement S n L ^ f)) =
      dualRep (hodgeDegrees h) (epsilonElement S n L) ^ f := by
    rw [kottwitzRep_inl, map_pow]
  rw [kottwitzFrobenius_eq, kottwitzFrobenius_eq, frobeniusElement_mul_epsilonElement, map_mul,
    hinl]
  refine LinearMap.ext fun y => ?_
  have hpow : ∀ (j : ℕ) (z : KottwitzSpace S n L (hodgeDegrees h)),
      (dualRep (hodgeDegrees h) (epsilonElement S n L) ^ j) z =
        (∏ τ, (((-1 : Lˣ) ^ (n - 1) : Lˣ) : L) ^ h (τ, false)) ^ j • z := by
    intro j
    induction j with
    | zero => intro z; simp
    | succ j ih =>
      intro z
      rw [pow_succ, LinearEquiv.mul_apply, dualRep_epsilonElement, map_smul, ih, smul_smul,
        pow_succ]
      exact congrArg (· • z) (mul_comm _ _)
  simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply, hpow, smul_smul]
  congr 1
  rw [Units.val_neg, neg_pow, mul_assoc, mul_comm ((s : L) ^ _), ← mul_assoc,
    sign_cancel h hsum f, one_mul]

theorem kottwitzCharpoly_neg (s : Lˣ) (x : DualGroup S n L) :
    kottwitzCharpoly h hsum G f hGf (-s) (x * epsilonElement S n L) =
      kottwitzCharpoly h hsum G f hGf s x := by
  rw [kottwitzCharpoly, kottwitzCharpoly, kottwitzFrobenius_neg]

/-- Replacing `√p` by `-√p` and `x` by `x ε̂` does not change `V`. -/
theorem kottwitzV_neg (s : Lˣ) (x : DualGroup S n L) :
    kottwitzV h hsum G f hGf (-s) (x * epsilonElement S n L) = kottwitzV h hsum G f hGf s x :=
  MonoidHom.ext_mint (LinearEquiv.toLinearMap_injective (kottwitzFrobenius_neg h hsum G f hGf s x))

theorem cocharPairing_mul_epsilonHat (t : Lˣ × (S → Fin n → Lˣ)) (a : ℤ × (S → Fin n → ℤ)) :
    cocharPairing (t * epsilonHat S n L) a = cocharPairing t a * (-1) ^ twoRhoPairing a := by
  rw [cocharPairing_mul, cocharPairing_epsilonHat]

end Sign

/-! ### Kottwitz's `V(π_p, E_v)` and `P(π_p, E_v)` for an unramified representation -/

section Parameters

open KottwitzUnramified Langlands.Global.AdelicFunctoriality

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [Algebra.IsQuadraticExtension E K]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {σ : SecondKindInvolution E K A} {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- The embedding coordinates `(a₀, (a_{τ,k}))` of a `ℚ_p`-rational cocharacter `(m, m_c)`
of the diagonal torus: `a₀ = m_c` and `a_{τ,k} = m_{w(Φτ), k}`, where `w(i)` is the place
of `K` above `p` determined by `θ ∘ i` (the Library's `harrisPlace`). -/
def embeddingCochar (θ : ℂ →+* PadicAlgCl p) (Φ : (E →+* ℝ) → (K →+* ℂ))
    (m : localCocharacters E K (rationalPrimePlace p) n) : ℤ × ((E →+* ℝ) → Fin n → ℤ) :=
  (m.1.2, fun τ k => m.1.1 (harrisPlace p θ (Φ τ)) k)

variable (c : UnramifiedChart σ (rationalPrimePlace p) n) (θ : ℂ →+* PadicAlgCl p)
  {Φ : (E →+* ℝ) → (K →+* ℂ)} (hΦ : IsCMSection E K Φ)

/-- `t̂ = (ζ, (s_{τ,k}))` lifts the unitarily normalized character `χ = ξ δ_B^{-1/2}` of the
principal-series character `ξ`: `λ(t̂) = χ(λ(p)) = ξ(λ(p)) · (√p)^{⟨2ρ, λ⟩}` for every
`ℚ_p`-rational cocharacter `λ`. -/
def IsNormalizedLift {Ω : Type uΩ} [Field Ω] (s : SqrtPrime (rationalPrimePlace p) Ω)
    (ξ : c.torus →* Ωˣ) (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) : Prop :=
  ∀ m : localCocharacters E K (rationalPrimePlace p) n,
    cocharPairing t (embeddingCochar θ Φ m) =
      ξ (c.cocharHom (Multiplicative.ofAdd m)) * s.1 ^ twoRhoPairing (embeddingCochar θ Φ m)

/-- Changing `√p` to `-√p` is compensated by `t̂ ↦ t̂ ε̂`. -/
theorem IsNormalizedLift.neg {Ω : Type uΩ} [Field Ω] {s : SqrtPrime (rationalPrimePlace p) Ω}
    {ξ : c.torus →* Ωˣ} {t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)}
    (ht : IsNormalizedLift c θ (Φ := Φ) s ξ t) :
    IsNormalizedLift c θ (Φ := Φ) s.neg ξ (t * epsilonHat (E →+* ℝ) n Ω) := by
  intro m
  rw [cocharPairing_mul_epsilonHat, ht m, mul_assoc]
  congr 1
  change _ = (-s.1) ^ _
  rw [← mul_zpow, mul_neg_one]

/-- Kottwitz's function `i ↦ n(i)`, read on the CM indices of `Φ`. -/
def cmHodge (nfun : (K →+* ℂ) → ℕ) : (E →+* ℝ) × Bool → ℕ :=
  fun x => nfun (cmFactorEmbeddingEquiv Φ hΦ x)

theorem cmHodge_add (nfun : (K →+* ℂ) → ℕ)
    (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n) (τ : E →+* ℝ) :
    cmHodge hΦ nfun (τ, true) + cmHodge hΦ nfun (τ, false) = n := by
  have h := hconj (cmFactorEmbeddingEquiv Φ hΦ (τ, true))
  rw [← cmFactorEmbeddingEquiv_cmSwap hΦ] at h
  exact h

theorem ofEmbeddingPerm_pow_apply (F : Equiv.Perm (K →+* ℂ))
    (hF : ∀ i, F (ComplexEmbedding.conjugate i) = ComplexEmbedding.conjugate (F i)) (j : ℕ)
    (x : (E →+* ℝ) × Bool) :
    ((CMPerm.ofEmbeddingPerm hΦ F hF ^ j : CMPerm (E →+* ℝ)) : Equiv.Perm _) x =
      (cmFactorEmbeddingEquiv Φ hΦ).symm ((F ^ j) (cmFactorEmbeddingEquiv Φ hΦ x)) := by
  induction j generalizing x with
  | zero =>
    rw [pow_zero, Subgroup.coe_one, Equiv.Perm.one_apply, pow_zero, Equiv.Perm.one_apply,
      Equiv.symm_apply_apply]
  | succ j ih =>
    rw [pow_succ, Subgroup.coe_mul, Equiv.Perm.mul_apply, ih, CMPerm.ofEmbeddingPerm_apply,
      pow_succ, Equiv.Perm.mul_apply]

variable (p) in
/-- The local degree `f_v` of the reflex field at the place `v` defined by `θ`
(`hodgeOrbitDegree` of the Frobenius permutation and Kottwitz's function). -/
abbrev localDegree (nfun : (K →+* ℂ) → ℕ) : ℕ :=
  hodgeOrbitDegree (frobeniusPerm K p θ) nfun

theorem cmHodge_frobenius_pow (nfun : (K →+* ℂ) → ℕ) (x : (E →+* ℝ) × Bool) :
    cmHodge hΦ nfun (((frobeniusCMPerm hΦ θ ^ localDegree p θ nfun : CMPerm (E →+* ℝ)) :
      Equiv.Perm _) x) = cmHodge hΦ nfun x := by
  rw [frobeniusCMPerm, ofEmbeddingPerm_pow_apply, cmHodge, cmHodge, Equiv.apply_symm_apply]
  exact hodgeOrbitDegree_preserves _ _ _

/-- Kottwitz's polynomial `det(X - Z(Φ_v) r(N_f(t̂) ⋊ Φ_v))` attached to the dual-torus
element `t̂`, the place `v` of the reflex field determined by `θ`, and `√p = s`. -/
def kottwitzPolynomialOf (nfun : (K →+* ℂ) → ℕ)
    (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n) {Ω : Type uΩ} [Field Ω]
    (s : Ωˣ) (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) : Polynomial Ω :=
  kottwitzCharpoly (cmHodge hΦ nfun) (cmHodge_add hΦ nfun hconj) (frobeniusCMPerm hΦ θ)
    (localDegree p θ nfun) (cmHodge_frobenius_pow θ hΦ nfun) s (torusElement t)

theorem kottwitzPolynomialOf_neg (nfun : (K →+* ℂ) → ℕ)
    (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n) {Ω : Type uΩ} [Field Ω]
    (s : Ωˣ) (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) :
    kottwitzPolynomialOf θ hΦ nfun hconj (-s) (t * epsilonHat (E →+* ℝ) n Ω) =
      kottwitzPolynomialOf θ hΦ nfun hconj s t := by
  rw [kottwitzPolynomialOf, kottwitzPolynomialOf, torusElement_mul]
  exact kottwitzCharpoly_neg _ _ _ _ _ s (torusElement t)

/-- Kottwitz's unramified representation `V = (r ∘ φ_{E_v}) ⊗ Z` of the unramified quotient
`ℤ` of `W_{E_v}` (generator: geometric Frobenius `Φ_v`) attached to the dual-torus element
`t̂`, the place `v` determined by `θ`, and `√p = s`. -/
def kottwitzRepresentationOf (nfun : (K →+* ℂ) → ℕ)
    (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n) {Ω : Type uΩ} [Field Ω]
    (s : Ωˣ) (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) :
    Multiplicative ℤ →* (KottwitzSpace (E →+* ℝ) n Ω (hodgeDegrees (cmHodge hΦ nfun)) ≃ₗ[Ω]
      KottwitzSpace (E →+* ℝ) n Ω (hodgeDegrees (cmHodge hΦ nfun))) :=
  kottwitzV (cmHodge hΦ nfun) (cmHodge_add hΦ nfun hconj) (frobeniusCMPerm hΦ θ)
    (localDegree p θ nfun) (cmHodge_frobenius_pow θ hΦ nfun) s (torusElement t)

theorem kottwitzRepresentationOf_neg (nfun : (K →+* ℂ) → ℕ)
    (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n) {Ω : Type uΩ} [Field Ω]
    (s : Ωˣ) (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) :
    kottwitzRepresentationOf θ hΦ nfun hconj (-s) (t * epsilonHat (E →+* ℝ) n Ω) =
      kottwitzRepresentationOf θ hΦ nfun hconj s t := by
  rw [kottwitzRepresentationOf, kottwitzRepresentationOf, torusElement_mul]
  exact kottwitzV_neg _ _ _ _ _ s (torusElement t)

/-- `P(t̂)` is the characteristic polynomial (in the standard basis of `W`) of the image of
geometric Frobenius `Φ_v` under `V(t̂)`. -/
theorem kottwitzPolynomialOf_eq (nfun : (K →+* ℂ) → ℕ)
    (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n) {Ω : Type uΩ} [Field Ω]
    (s : Ωˣ) (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) :
    kottwitzPolynomialOf θ hΦ nfun hconj s t =
      open scoped Classical in
      (LinearMap.toMatrix (kottwitzBasis n Ω _) (kottwitzBasis n Ω _)
        (kottwitzRepresentationOf θ hΦ nfun hconj s t
          (Multiplicative.ofAdd 1)).toLinearMap).charpoly :=
  rfl

variable [Module.Finite ℚ A] {L : Type uL} [Field L]

/-- `V` is Kottwitz's unramified representation `V(π_p, E_v)` over the extension `Ω` of `L`
(for the place `v` determined by `θ` and the square root `s` of `p` in `Ω`): it is
`V(t̂)` for a lift `t̂` of the unitarily normalized character of some principal-series
parameter `ξ` of `π` with values in `Ω`. -/
def IsKottwitzRepresentationOver (nfun : (K →+* ℂ) → ℕ)
    (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n)
    (π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p)))
    (Ω : Type uΩ) [Field Ω] [Algebra L Ω] (s : SqrtPrime (rationalPrimePlace p) Ω)
    (V : Multiplicative ℤ →* (KottwitzSpace (E →+* ℝ) n Ω (hodgeDegrees (cmHodge hΦ nfun)) ≃ₗ[Ω]
      KottwitzSpace (E →+* ℝ) n Ω (hodgeDegrees (cmHodge hΦ nfun)))) : Prop :=
  ∃ (ξ : c.torus →* Ωˣ) (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)),
    c.HasPrincipalSeriesParameter π ξ ∧ IsNormalizedLift c θ (Φ := Φ) s ξ t ∧
      V = kottwitzRepresentationOf θ hΦ nfun hconj s.1 t

/-- `P` is Kottwitz's polynomial `P(π_p, E_v)` over the extension `Ω` of `L`, for the place
`v` of the reflex field determined by `θ` and the square root `s` of `p` in `Ω`: for some
principal-series parameter `ξ` of `π` with values in `Ω` and some lift `t̂` of its unitarily
normalized character, `P` is the characteristic polynomial of geometric Frobenius
`Φ_v` on `V(π_p, E_v) = (r ∘ φ_{E_v}) ⊗ Z`, where `φ(Frob) = t̂ ⋊ Frob`. -/
def IsKottwitzPolynomialOver (nfun : (K →+* ℂ) → ℕ)
    (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n)
    (π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p)))
    (Ω : Type uΩ) [Field Ω] [Algebra L Ω] (s : SqrtPrime (rationalPrimePlace p) Ω)
    (P : Polynomial Ω) : Prop :=
  ∃ (ξ : c.torus →* Ωˣ) (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)),
    c.HasPrincipalSeriesParameter π ξ ∧ IsNormalizedLift c θ (Φ := Φ) s ξ t ∧
      P = kottwitzPolynomialOf θ hΦ nfun hconj s.1 t

/-- Kottwitz's `P(π_p, E_v) ∈ L[X]`: its image in `L̄[X]` is Kottwitz's polynomial over
`L̄ = AlgebraicClosure L`. -/
def IsKottwitzPolynomial (nfun : (K →+* ℂ) → ℕ)
    (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n)
    (π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p)))
    (s : SqrtPrime (rationalPrimePlace p) (AlgebraicClosure L)) (P : Polynomial L) : Prop :=
  IsKottwitzPolynomialOver c θ hΦ nfun hconj π (AlgebraicClosure L) s
    (P.map (algebraMap L (AlgebraicClosure L)))

variable {c θ hΦ}

/-- `P(π_p, E_v)` is monic. -/
theorem IsKottwitzPolynomialOver.monic {nfun : (K →+* ℂ) → ℕ}
    {hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n}
    {π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p))}
    {Ω : Type uΩ} [Field Ω] [Algebra L Ω] {s : SqrtPrime (rationalPrimePlace p) Ω}
    {P : Polynomial Ω} (hP : IsKottwitzPolynomialOver c θ hΦ nfun hconj π Ω s P) : P.Monic := by
  obtain ⟨ξ, t, -, -, rfl⟩ := hP
  exact kottwitzCharpoly_monic _ _ _ _ _ _ _

/-- `P(π_p, E_v)` has degree `dim r = ∏_τ C(n, n(Φτ̄))`. -/
theorem IsKottwitzPolynomialOver.natDegree_eq {nfun : (K →+* ℂ) → ℕ}
    {hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n}
    {π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p))}
    {Ω : Type uΩ} [Field Ω] [Algebra L Ω] {s : SqrtPrime (rationalPrimePlace p) Ω}
    {P : Polynomial Ω} (hP : IsKottwitzPolynomialOver c θ hΦ nfun hconj π Ω s P) :
    P.natDegree = kottwitzDim n (hodgeDegrees (cmHodge hΦ nfun)) := by
  obtain ⟨ξ, t, -, -, rfl⟩ := hP
  exact kottwitzCharpoly_natDegree _ _ _ _ _ _ _

theorem SqrtPrime.neg_neg {Ω : Type uΩ} [Field Ω] (r : SqrtPrime (rationalPrimePlace p) Ω) :
    r.neg.neg = r :=
  Subtype.ext (_root_.neg_neg r.1)

/-- The two square roots of `p` in a field. -/
theorem SqrtPrime.eq_or_eq_neg {Ω : Type uΩ} [Field Ω] (s s' : SqrtPrime (rationalPrimePlace p) Ω) :
    s' = s ∨ s' = s.neg := by
  have h : ((s'.1 : Ω)) ^ 2 = ((s.1 : Ω)) ^ 2 := by rw [s'.2, s.2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact Or.inl (Subtype.ext (Units.ext h))
  · exact Or.inr (Subtype.ext (Units.ext (by rw [h]; rfl)))

theorem IsKottwitzPolynomialOver.neg {nfun : (K →+* ℂ) → ℕ}
    {hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n}
    {π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p))}
    {Ω : Type uΩ} [Field Ω] [Algebra L Ω] {s : SqrtPrime (rationalPrimePlace p) Ω}
    {P : Polynomial Ω} (hP : IsKottwitzPolynomialOver c θ hΦ nfun hconj π Ω s P) :
    IsKottwitzPolynomialOver c θ hΦ nfun hconj π Ω s.neg P := by
  obtain ⟨ξ, t, hξ, ht, rfl⟩ := hP
  exact ⟨ξ, t * epsilonHat (E →+* ℝ) n Ω, hξ, ht.neg, (kottwitzPolynomialOf_neg θ hΦ nfun hconj
    s.1 t).symm⟩

/-- Kottwitz (p.656): `P(π_p, E_v)` does not depend on the choice of `√p`. -/
theorem isKottwitzPolynomialOver_iff_of_sqrtPrime {nfun : (K →+* ℂ) → ℕ}
    {hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n}
    {π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p))}
    {Ω : Type uΩ} [Field Ω] [Algebra L Ω] (s s' : SqrtPrime (rationalPrimePlace p) Ω)
    (P : Polynomial Ω) :
    IsKottwitzPolynomialOver c θ hΦ nfun hconj π Ω s P ↔
      IsKottwitzPolynomialOver c θ hΦ nfun hconj π Ω s' P := by
  rcases SqrtPrime.eq_or_eq_neg s s' with h | h
  · rw [h]
  · rw [h]
    refine ⟨fun hP => hP.neg, fun hP => ?_⟩
    have h2 := hP.neg
    rwa [SqrtPrime.neg_neg] at h2

/-- The relation only depends on the isomorphism class of `π`. -/
theorem IsKottwitzPolynomialOver.of_equiv {nfun : (K →+* ℂ) → ℕ}
    {hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n}
    {π π' : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p))}
    (e : π.representation.Equiv π'.representation)
    {Ω : Type uΩ} [Field Ω] [Algebra L Ω] {s : SqrtPrime (rationalPrimePlace p) Ω}
    {P : Polynomial Ω} (hP : IsKottwitzPolynomialOver c θ hΦ nfun hconj π Ω s P) :
    IsKottwitzPolynomialOver c θ hΦ nfun hconj π' Ω s P := by
  obtain ⟨ξ, t, hξ, ht, rfl⟩ := hP
  exact ⟨ξ, t, UnramifiedChart.HasPrincipalSeriesParameter.of_equiv c e hξ, ht, rfl⟩

/-- `P(π_p, E_v) ∈ L[X]` is monic of degree `dim r`. -/
theorem IsKottwitzPolynomial.monic_and_natDegree {nfun : (K →+* ℂ) → ℕ}
    {hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n}
    {π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p))}
    {s : SqrtPrime (rationalPrimePlace p) (AlgebraicClosure L)} {P : Polynomial L}
    (hP : IsKottwitzPolynomial c θ hΦ nfun hconj π s P) :
    P.Monic ∧ P.natDegree = kottwitzDim n (hodgeDegrees (cmHodge hΦ nfun)) := by
  refine ⟨Polynomial.monic_map_iff.mp hP.monic, ?_⟩
  rw [← hP.natDegree_eq, Polynomial.natDegree_map]

/-- `P(π_p, E_v) ∈ L[X]` does not depend on the choice of `√p ∈ L̄`. -/
theorem isKottwitzPolynomial_iff_of_sqrtPrime {nfun : (K →+* ℂ) → ℕ}
    {hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n}
    {π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p))}
    (s s' : SqrtPrime (rationalPrimePlace p) (AlgebraicClosure L)) (P : Polynomial L) :
    IsKottwitzPolynomial c θ hΦ nfun hconj π s P ↔
      IsKottwitzPolynomial c θ hΦ nfun hconj π s' P :=
  isKottwitzPolynomialOver_iff_of_sqrtPrime s s' _

/-- Kottwitz (p.656): `V(π_p, E_v)` does not depend on the choice of `√p`. -/
theorem isKottwitzRepresentationOver_iff_of_sqrtPrime {nfun : (K →+* ℂ) → ℕ}
    {hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n}
    {π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p))}
    {Ω : Type uΩ} [Field Ω] [Algebra L Ω] (s s' : SqrtPrime (rationalPrimePlace p) Ω)
    (V : Multiplicative ℤ →* (KottwitzSpace (E →+* ℝ) n Ω (hodgeDegrees (cmHodge hΦ nfun)) ≃ₗ[Ω]
      KottwitzSpace (E →+* ℝ) n Ω (hodgeDegrees (cmHodge hΦ nfun)))) :
    IsKottwitzRepresentationOver c θ hΦ nfun hconj π Ω s V ↔
      IsKottwitzRepresentationOver c θ hΦ nfun hconj π Ω s' V := by
  have key : ∀ r : SqrtPrime (rationalPrimePlace p) Ω,
      IsKottwitzRepresentationOver c θ hΦ nfun hconj π Ω r V →
        IsKottwitzRepresentationOver c θ hΦ nfun hconj π Ω r.neg V := by
    rintro r ⟨ξ, t, hξ, ht, rfl⟩
    exact ⟨ξ, t * epsilonHat (E →+* ℝ) n Ω, hξ, ht.neg,
      (kottwitzRepresentationOf_neg θ hΦ nfun hconj r.1 t).symm⟩
  rcases SqrtPrime.eq_or_eq_neg s s' with h | h
  · rw [h]
  · rw [h]
    refine ⟨key s, fun hV => ?_⟩
    have h2 := key _ hV
    rwa [SqrtPrime.neg_neg] at h2

/-- Kottwitz's polynomial is the characteristic polynomial of `Φ_v` on `V(π_p, E_v)`. -/
theorem isKottwitzPolynomialOver_iff {nfun : (K →+* ℂ) → ℕ}
    {hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n}
    {π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p))}
    {Ω : Type uΩ} [Field Ω] [Algebra L Ω] (s : SqrtPrime (rationalPrimePlace p) Ω)
    (P : Polynomial Ω) :
    IsKottwitzPolynomialOver c θ hΦ nfun hconj π Ω s P ↔
      ∃ V, IsKottwitzRepresentationOver c θ hΦ nfun hconj π Ω s V ∧
        open scoped Classical in
        P = (LinearMap.toMatrix (kottwitzBasis n Ω _) (kottwitzBasis n Ω _)
          (V (Multiplicative.ofAdd 1)).toLinearMap).charpoly := by
  constructor
  · rintro ⟨ξ, t, hξ, ht, rfl⟩
    exact ⟨_, ⟨ξ, t, hξ, ht, rfl⟩, kottwitzPolynomialOf_eq θ hΦ nfun hconj s.1 t⟩
  · rintro ⟨V, ⟨ξ, t, hξ, ht, rfl⟩, rfl⟩
    exact ⟨ξ, t, hξ, ht, (kottwitzPolynomialOf_eq θ hΦ nfun hconj s.1 t).symm⟩

end Parameters

end Langlands.Shimura.KottwitzDual
