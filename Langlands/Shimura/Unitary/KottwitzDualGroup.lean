import Langlands.Shimura.Unitary.CMEmbeddingIndices
import Langlands.Weil.Local.Assembly
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Kottwitz's unitary similitude groups: dual group and unramified L-group

The dual group `Ĝ(L) = Lˣ × ∏_{τ} GL_n(L)` of the unitary similitude group of
a CM field, written in the coordinates of a CM type indexed by the real places
`τ`; the action of a conjugation-compatible permutation of the complex
embeddings by pinned automorphisms; the unramified L-group `Ĝ ⋊ ℤ`; and the
geometric Frobenius permutation of the complex embeddings attached to an
embedding `θ : ℂ → Q̄_p`. See the paired Markdown for conventions and sources.
-/

noncomputable section

open NumberField

namespace Langlands.Shimura.KottwitzDual

universe u v w

/-! ### Permutations of the CM factor indices commuting with conjugation -/

section CMPerm

variable (S : Type u)

/-- Complex conjugation on the CM factor indices: `(τ, b) ↦ (τ, !b)`. -/
def cmSwap : Equiv.Perm (S × Bool) where
  toFun x := (x.1, !x.2)
  invFun x := (x.1, !x.2)
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem cmSwap_apply (x : S × Bool) : cmSwap S x = (x.1, !x.2) := rfl

/-- Permutations of `S × Bool` commuting with conjugation. -/
abbrev CMPerm : Subgroup (Equiv.Perm (S × Bool)) :=
  Subgroup.centralizer {cmSwap S}

variable {S}

theorem CMPerm.apply_cmSwap (G : CMPerm S) (x : S × Bool) :
    (G : Equiv.Perm (S × Bool)) (cmSwap S x) = cmSwap S ((G : Equiv.Perm (S × Bool)) x) := by
  have h := (Subgroup.mem_centralizer_iff.mp G.2) (cmSwap S) rfl
  exact (congrArg (fun e : Equiv.Perm (S × Bool) => e x) h).symm

/-- Whether `G` moves the selected embedding `(τ, true)` to a conjugate one. -/
def CMPerm.crosses (G : CMPerm S) (τ : S) : Bool :=
  !((G : Equiv.Perm (S × Bool)) (τ, true)).2

theorem CMPerm.apply_eq (G : CMPerm S) (τ : S) (b : Bool) :
    (G : Equiv.Perm (S × Bool)) (τ, b) =
      (((G : Equiv.Perm (S × Bool)) (τ, true)).1, xor b (CMPerm.crosses G τ)) := by
  cases b
  · have h := CMPerm.apply_cmSwap G (τ, true)
    simp only [cmSwap_apply, Bool.not_true] at h
    rw [h]
    simp [CMPerm.crosses]
  · simp [CMPerm.crosses]

/-- The underlying function on real places. -/
def CMPerm.baseFun (G : CMPerm S) (τ : S) : S :=
  ((G : Equiv.Perm (S × Bool)) (τ, true)).1

theorem CMPerm.baseFun_mul (G H : CMPerm S) (τ : S) :
    CMPerm.baseFun (G * H) τ = CMPerm.baseFun G (CMPerm.baseFun H τ) := by
  simp only [CMPerm.baseFun, Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [CMPerm.apply_eq H τ true, CMPerm.apply_eq G]

theorem CMPerm.crosses_mul (G H : CMPerm S) (τ : S) :
    CMPerm.crosses (G * H) τ =
      xor (CMPerm.crosses H τ) (CMPerm.crosses G (CMPerm.baseFun H τ)) := by
  have h : ((G * H : CMPerm S) : Equiv.Perm (S × Bool)) (τ, true) =
      (G : Equiv.Perm (S × Bool)) (CMPerm.baseFun H τ, xor true (CMPerm.crosses H τ)) := by
    rw [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, CMPerm.apply_eq H τ true]
    rfl
  conv_lhs => rw [CMPerm.crosses, h, CMPerm.apply_eq G]
  generalize CMPerm.crosses H τ = a
  generalize CMPerm.crosses G (CMPerm.baseFun H τ) = b
  cases a <;> cases b <;> rfl

theorem CMPerm.baseFun_one (τ : S) : CMPerm.baseFun (1 : CMPerm S) τ = τ := rfl

theorem CMPerm.crosses_one (τ : S) : CMPerm.crosses (1 : CMPerm S) τ = false := rfl

/-- The permutation of real places underlying a conjugation-compatible permutation. -/
def CMPerm.base : CMPerm S →* Equiv.Perm S where
  toFun G :=
    { toFun := CMPerm.baseFun G
      invFun := CMPerm.baseFun G⁻¹
      left_inv := fun τ => by rw [← CMPerm.baseFun_mul, inv_mul_cancel, CMPerm.baseFun_one]
      right_inv := fun τ => by rw [← CMPerm.baseFun_mul, mul_inv_cancel, CMPerm.baseFun_one] }
  map_one' := rfl
  map_mul' G H := Equiv.ext fun τ => CMPerm.baseFun_mul G H τ

@[simp] theorem CMPerm.base_apply (G : CMPerm S) (τ : S) :
    CMPerm.base G τ = CMPerm.baseFun G τ := rfl

end CMPerm

/-! ### The pinned outer involution of `GL_n` -/

section Twist

variable (n : ℕ) (L : Type v) [Field L]

/-- The antidiagonal matrix with alternating signs, `J'_{k, n-1-k} = (-1)^k`. -/
def signedAntidiagonal : Matrix (Fin n) (Fin n) L :=
  fun k l => if l = Fin.rev k then (-1) ^ (k : ℕ) else 0

theorem signedAntidiagonal_mul_transpose :
    signedAntidiagonal n L * (signedAntidiagonal n L).transpose = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, signedAntidiagonal, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.rev k)]
  · by_cases h : k = l
    · subst h; simp [← pow_add, ← two_mul, pow_mul]
    · have : Fin.rev k ≠ Fin.rev l := fun e => h (Fin.rev_injective e)
      simp [h, this]
  · intro j _ hj; simp [hj]
  · simp

theorem signedAntidiagonal_transpose_mul :
    (signedAntidiagonal n L).transpose * signedAntidiagonal n L = 1 :=
  mul_eq_one_comm.mp (signedAntidiagonal_mul_transpose n L)

/-- `J'` as an element of `GL_n(L)`. -/
def signedAntidiagonalUnit : GL (Fin n) L :=
  ⟨signedAntidiagonal n L, (signedAntidiagonal n L).transpose,
    signedAntidiagonal_mul_transpose n L, signedAntidiagonal_transpose_mul n L⟩

/-- The square of `J'` is the scalar `(-1)^(n-1)`. -/
theorem signedAntidiagonal_mul_self :
    signedAntidiagonal n L * signedAntidiagonal n L =
      Matrix.scalar (Fin n) ((-1 : L) ^ (n - 1)) := by
  ext k l
  simp only [Matrix.mul_apply, signedAntidiagonal, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (Fin.rev k)]
  · by_cases h : k = l
    · subst h
      simp only [Fin.rev_rev, ↓reduceIte]
      rw [← pow_add, Fin.val_rev]
      congr 1
      omega
    · simp [h, Ne.symm h]
  · intro j _ hj; simp [hj]
  · simp

/-- Inverse transpose, a group endomorphism of `GL_n(L)`. -/
def transposeInv : GL (Fin n) L →* GL (Fin n) L where
  toFun g := ⟨(g⁻¹ : GL (Fin n) L).val.transpose, (g : Matrix (Fin n) (Fin n) L).transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by ext : 1; simp
  map_mul' g h := by
    ext : 1
    simp [Matrix.transpose_mul, mul_inv_rev]

@[simp] theorem transposeInv_val (g : GL (Fin n) L) :
    (transposeInv n L g : Matrix (Fin n) (Fin n) L) = (g⁻¹ : GL (Fin n) L).val.transpose := rfl

theorem transposeInv_transposeInv (g : GL (Fin n) L) :
    transposeInv n L (transposeInv n L g) = g := by
  ext : 1
  simp only [transposeInv_val]
  have : (transposeInv n L g)⁻¹ = ⟨(g : Matrix (Fin n) (Fin n) L).transpose,
      (g⁻¹ : GL (Fin n) L).val.transpose, by
        rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩ := by
    rw [inv_eq_iff_mul_eq_one]; ext : 1
    simp [← Matrix.transpose_mul]
  rw [this]
  simp

/-- The pinned outer involution `θ(g) = J' (g⁻¹)ᵀ J'⁻¹` of `GL_n`. -/
def twist : GL (Fin n) L →* GL (Fin n) L :=
  (MulAut.conj (signedAntidiagonalUnit n L)).toMonoidHom.comp (transposeInv n L)

theorem twist_apply (g : GL (Fin n) L) :
    twist n L g = signedAntidiagonalUnit n L * transposeInv n L g *
      (signedAntidiagonalUnit n L)⁻¹ := rfl

theorem transposeInv_signedAntidiagonalUnit :
    transposeInv n L (signedAntidiagonalUnit n L) = signedAntidiagonalUnit n L := by
  ext : 1
  simp only [transposeInv_val]
  have : (signedAntidiagonalUnit n L)⁻¹ = ⟨(signedAntidiagonal n L).transpose,
      signedAntidiagonal n L, signedAntidiagonal_transpose_mul n L,
      signedAntidiagonal_mul_transpose n L⟩ := rfl
  rw [this]
  simp [signedAntidiagonalUnit]

/-- The square of `J'` is central, so conjugation by it is trivial. -/
theorem signedAntidiagonalUnit_mul_self_comm (g : GL (Fin n) L) :
    signedAntidiagonalUnit n L * signedAntidiagonalUnit n L * g =
      g * (signedAntidiagonalUnit n L * signedAntidiagonalUnit n L) := by
  ext : 1
  simp only [Units.val_mul]
  change signedAntidiagonal n L * signedAntidiagonal n L * _ =
    _ * (signedAntidiagonal n L * signedAntidiagonal n L)
  rw [signedAntidiagonal_mul_self]
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

/-- `θ` is an involution. -/
theorem twist_twist (g : GL (Fin n) L) : twist n L (twist n L g) = g := by
  rw [twist_apply, twist_apply, map_mul, map_mul, map_inv, transposeInv_transposeInv,
    transposeInv_signedAntidiagonalUnit]
  set J := signedAntidiagonalUnit n L
  have hJ := signedAntidiagonalUnit_mul_self_comm n L g
  calc J * (J * g * J⁻¹) * J⁻¹ = (J * J * g) * (J⁻¹ * J⁻¹) := by group
    _ = (g * (J * J)) * (J⁻¹ * J⁻¹) := by rw [hJ]
    _ = g := by group

/-- `det θ(g) = (det g)⁻¹`. -/
theorem det_twist (g : GL (Fin n) L) :
    Matrix.GeneralLinearGroup.det (twist n L g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [twist_apply, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_transpose]

end Twist

/-! ### The dual group and its pinned automorphisms -/

section DualGroup

variable (S : Type u) [Fintype S] (n : ℕ) (L : Type v) [Field L]

/-- The dual group `Ĝ(L) = Lˣ × ∏_{τ ∈ S} GL_n(L)`: the first factor is dual to
the similitude factor, the factor at `τ` belongs to the selected CM embedding
`(τ, true)`. -/
abbrev DualGroup : Type (max u v) := Lˣ × (S → GL (Fin n) L)

variable {S n L}

/-- The underlying endomorphism of the action of `G` on `Ĝ`. -/
def dualEndo (G : CMPerm S) : DualGroup S n L →* DualGroup S n L where
  toFun x :=
    (x.1 * ∏ τ, (if CMPerm.crosses G τ then Matrix.GeneralLinearGroup.det (x.2 τ) else 1),
      fun τ' =>
        if CMPerm.crosses G ((CMPerm.base G).symm τ') then twist n L (x.2 ((CMPerm.base G).symm τ'))
        else x.2 ((CMPerm.base G).symm τ'))
  map_one' := by
    ext1
    · simp
    · funext τ'; simp
  map_mul' x y := by
    ext1
    · simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul]
      simp_rw [show ∀ τ, (if CMPerm.crosses G τ then Matrix.GeneralLinearGroup.det (x.2 τ) *
          Matrix.GeneralLinearGroup.det (y.2 τ) else 1) =
          (if CMPerm.crosses G τ then Matrix.GeneralLinearGroup.det (x.2 τ) else 1) *
          (if CMPerm.crosses G τ then Matrix.GeneralLinearGroup.det (y.2 τ) else 1) from
        fun τ => by split_ifs <;> simp, Finset.prod_mul_distrib]
      ac_rfl
    · funext τ'
      simp only [Prod.snd_mul, Pi.mul_apply, map_mul]
      split_ifs <;> rfl

theorem dualEndo_fst (G : CMPerm S) (x : DualGroup S n L) :
    (dualEndo G x).1 =
      x.1 * ∏ τ, (if CMPerm.crosses G τ then Matrix.GeneralLinearGroup.det (x.2 τ) else 1) := rfl

theorem dualEndo_snd_base (G : CMPerm S) (x : DualGroup S n L) (τ : S) :
    (dualEndo G x).2 (CMPerm.base G τ) =
      if CMPerm.crosses G τ then twist n L (x.2 τ) else x.2 τ := by
  simp only [dualEndo, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.symm_apply_apply]

theorem det_dualEndo_snd_base (G : CMPerm S) (x : DualGroup S n L) (τ : S) :
    Matrix.GeneralLinearGroup.det ((dualEndo G x).2 (CMPerm.base G τ)) =
      if CMPerm.crosses G τ then (Matrix.GeneralLinearGroup.det (x.2 τ))⁻¹
      else Matrix.GeneralLinearGroup.det (x.2 τ) := by
  rw [dualEndo_snd_base]
  split_ifs
  · exact det_twist n L _
  · rfl

theorem dualEndo_one : dualEndo (n := n) (L := L) (1 : CMPerm S) = MonoidHom.id _ := by
  ext x
  · simp [dualEndo_fst, CMPerm.crosses_one]
  · simp [dualEndo, CMPerm.crosses_one]
    rfl

theorem dualEndo_mul (G H : CMPerm S) :
    dualEndo (n := n) (L := L) (G * H) = (dualEndo G).comp (dualEndo H) := by
  ext x : 1
  ext1
  · simp only [MonoidHom.comp_apply, dualEndo_fst, mul_assoc]
    congr 1
    -- reindex the second product along the base permutation of `H`
    rw [← Equiv.prod_comp (CMPerm.base H) (fun σ => if CMPerm.crosses G σ then
      Matrix.GeneralLinearGroup.det ((dualEndo H x).2 σ) else 1), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [det_dualEndo_snd_base, CMPerm.crosses_mul, CMPerm.base_apply]
    cases CMPerm.crosses H τ <;> cases CMPerm.crosses G (CMPerm.baseFun H τ) <;> simp
  · funext τ''
    obtain ⟨τ, rfl⟩ := (CMPerm.base (G * H)).surjective τ''
    rw [MonoidHom.comp_apply, dualEndo_snd_base]
    have hb : CMPerm.base (G * H) τ = CMPerm.base G (CMPerm.base H τ) := by
      rw [map_mul]; rfl
    rw [hb, dualEndo_snd_base, dualEndo_snd_base, CMPerm.crosses_mul]
    rw [CMPerm.base_apply]
    cases hH : CMPerm.crosses H τ <;> cases hG : CMPerm.crosses G (CMPerm.baseFun H τ) <;>
      simp [twist_twist]

variable (S n L)

/-- The action of conjugation-compatible permutations of the CM factor indices on
the dual group by pinned automorphisms. -/
def dualAction : CMPerm S →* MulAut (DualGroup S n L) where
  toFun G :=
    { toFun := dualEndo G
      invFun := dualEndo G⁻¹
      left_inv := fun x => by
        rw [← MonoidHom.comp_apply, ← dualEndo_mul, inv_mul_cancel, dualEndo_one]; rfl
      right_inv := fun x => by
        rw [← MonoidHom.comp_apply, ← dualEndo_mul, mul_inv_cancel, dualEndo_one]; rfl
      map_mul' := (dualEndo G).map_mul }
  map_one' := MulEquiv.ext fun x => by
    change dualEndo 1 x = x
    rw [dualEndo_one]; rfl
  map_mul' G H := MulEquiv.ext fun x => by
    change dualEndo (G * H) x = dualEndo G (dualEndo H x)
    rw [dualEndo_mul]; rfl

variable {S n L}

@[simp] theorem dualAction_apply (G : CMPerm S) (x : DualGroup S n L) :
    dualAction S n L G x = dualEndo G x := rfl

variable (S n L)

/-- The unramified L-group `Ĝ ⋊ ℤ`, the generator `ofAdd 1` acting through `G`. -/
abbrev LGroup (G : CMPerm S) : Type (max u v) :=
  DualGroup S n L ⋊[zpowersHom (MulAut (DualGroup S n L)) (dualAction S n L G)]
    Multiplicative ℤ

variable {S n L}

/-- The Frobenius element `1 ⋊ Φ` of the unramified L-group. -/
def LGroup.frob (G : CMPerm S) : LGroup S n L G :=
  SemidirectProduct.inr (Multiplicative.ofAdd 1)

/-- The inclusion of the L-group of the degree `f` extension: `(g, Φ^k) ↦ (g, Φ^{fk})`. -/
def LGroup.restrictionHom (G : CMPerm S) (f : ℕ) : LGroup S n L (G ^ f) →* LGroup S n L G :=
  SemidirectProduct.lift SemidirectProduct.inl
    (SemidirectProduct.inr.comp (zpowersHom _ (Multiplicative.ofAdd (f : ℤ))))
    (fun k => by
      ext x : 1
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply]
      rw [← map_inv, ← SemidirectProduct.inl_aut]
      congr 1
      simp only [zpowersHom_apply, map_pow, toAdd_zpow, toAdd_ofAdd, smul_eq_mul]
      rw [← zpow_natCast, ← zpow_mul, mul_comm])

end DualGroup

/-! ### Conjugation-compatible permutations of the complex embeddings -/

section Embeddings

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [Algebra.IsQuadraticExtension E K]
  {Φ : (E →+* ℝ) → (K →+* ℂ)} (hΦ : IsCMSection E K Φ)

omit [NumberField E] in
/-- Complex conjugation of complex embeddings is precomposition with the CM involution. -/
theorem conjugate_apply (i : K →+* ℂ) (x : K) :
    ComplexEmbedding.conjugate i x = i (cmConjugation E K x) := by
  rw [ComplexEmbedding.conjugate_coe_eq, embedding_cmConjugation]
  rfl

/-- Swapping the Boolean index is complex conjugation of the factor embedding. -/
theorem cmFactorEmbeddingEquiv_cmSwap (x : (E →+* ℝ) × Bool) :
    cmFactorEmbeddingEquiv Φ hΦ (cmSwap _ x) =
      ComplexEmbedding.conjugate (cmFactorEmbeddingEquiv Φ hΦ x) := by
  rcases x with ⟨τ, b⟩
  cases b <;> simp [cmFactorEmbedding]

theorem cmFactorEmbeddingEquiv_symm_conjugate (j : K →+* ℂ) :
    (cmFactorEmbeddingEquiv Φ hΦ).symm (ComplexEmbedding.conjugate j) =
      cmSwap _ ((cmFactorEmbeddingEquiv Φ hΦ).symm j) := by
  apply (cmFactorEmbeddingEquiv Φ hΦ).injective
  rw [Equiv.apply_symm_apply, cmFactorEmbeddingEquiv_cmSwap, Equiv.apply_symm_apply]

/-- A permutation of the complex embeddings commuting with complex conjugation,
transported to the CM factor indices `(E →+* ℝ) × Bool`. -/
def CMPerm.ofEmbeddingPerm (F : Equiv.Perm (K →+* ℂ))
    (hF : ∀ i, F (ComplexEmbedding.conjugate i) = ComplexEmbedding.conjugate (F i)) :
    CMPerm (E →+* ℝ) :=
  ⟨(cmFactorEmbeddingEquiv Φ hΦ).trans (F.trans (cmFactorEmbeddingEquiv Φ hΦ).symm), by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    ext x : 1
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.trans_apply]
    rw [cmFactorEmbeddingEquiv_cmSwap, hF, cmFactorEmbeddingEquiv_symm_conjugate]⟩

theorem CMPerm.ofEmbeddingPerm_apply (F : Equiv.Perm (K →+* ℂ))
    (hF : ∀ i, F (ComplexEmbedding.conjugate i) = ComplexEmbedding.conjugate (F i))
    (x : (E →+* ℝ) × Bool) :
    cmFactorEmbeddingEquiv Φ hΦ ((CMPerm.ofEmbeddingPerm hΦ F hF : Equiv.Perm _) x) =
      F (cmFactorEmbeddingEquiv Φ hΦ x) :=
  Equiv.apply_symm_apply _ _

end Embeddings

/-! ### Geometric Frobenius transported along `θ : ℂ → Q̄_p` -/

section Frobenius

variable (K : Type v) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-- Composition with a field embedding `θ : ℂ → Q̄_p` identifies the complex
embeddings of `K` with its `p`-adic embeddings. -/
def thetaEmbeddingEquiv (θ : ℂ →+* PadicAlgCl p) : (K →+* ℂ) ≃ (K →+* PadicAlgCl p) :=
  Equiv.ofBijective (fun i => θ.comp i) <| by
    have hinj : Function.Injective (fun i : K →+* ℂ => θ.comp i) := fun i j h =>
      RingHom.ext fun x => θ.injective (RingHom.congr_fun h x)
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
    rw [NumberField.Embeddings.card K ℂ, NumberField.Embeddings.card K (PadicAlgCl p)]

@[simp] theorem thetaEmbeddingEquiv_apply (θ : ℂ →+* PadicAlgCl p) (i : K →+* ℂ) :
    thetaEmbeddingEquiv K p θ i = θ.comp i := rfl

/-- The Library's chosen geometric Frobenius in `Gal(Q̄_p/ℚ_p)`: the image of
`localGeometricFrobenius` of `ℚ_p` in the absolute Galois group. -/
def geometricFrobenius : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p :=
  Weil.Local.localProjection (PadicField.rational p)
    (Weil.Local.localGeometricFrobenius (PadicField.rational p))

/-- Postcomposition with an automorphism of `Q̄_p` permutes the `p`-adic embeddings. -/
def padicEmbeddingPerm (a : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Equiv.Perm (K →+* PadicAlgCl p) where
  toFun j := (a : PadicAlgCl p →+* PadicAlgCl p).comp j
  invFun j := (a.symm : PadicAlgCl p →+* PadicAlgCl p).comp j
  left_inv j := RingHom.ext fun x => a.symm_apply_apply (j x)
  right_inv j := RingHom.ext fun x => a.apply_symm_apply (j x)

/-- Geometric Frobenius acting on the complex embeddings through `θ`:
`i ↦ θ⁻¹ ∘ Frob ∘ θ ∘ i`. -/
def frobeniusPerm (θ : ℂ →+* PadicAlgCl p) : Equiv.Perm (K →+* ℂ) :=
  (thetaEmbeddingEquiv K p θ).trans
    ((padicEmbeddingPerm K p (geometricFrobenius p)).trans (thetaEmbeddingEquiv K p θ).symm)

theorem theta_frobeniusPerm_apply (θ : ℂ →+* PadicAlgCl p) (i : K →+* ℂ) (x : K) :
    θ (frobeniusPerm K p θ i x) = geometricFrobenius p (θ (i x)) :=
  RingHom.congr_fun ((thetaEmbeddingEquiv K p θ).apply_symm_apply
    (padicEmbeddingPerm K p (geometricFrobenius p) (thetaEmbeddingEquiv K p θ i))) x

variable {E : Type u} [Field E] [NumberField E] [IsTotallyReal E]
  [IsTotallyComplex K] [Algebra E K] [Algebra.IsQuadraticExtension E K]

variable (E) in
include E in
omit [NumberField E] in
/-- The Frobenius permutation commutes with complex conjugation. -/
theorem frobeniusPerm_conjugate (θ : ℂ →+* PadicAlgCl p) (i : K →+* ℂ) :
    frobeniusPerm K p θ (ComplexEmbedding.conjugate i) =
      ComplexEmbedding.conjugate (frobeniusPerm K p θ i) := by
  apply (thetaEmbeddingEquiv K p θ).injective
  ext x
  change θ (frobeniusPerm K p θ _ x) = θ (ComplexEmbedding.conjugate (frobeniusPerm K p θ i) x)
  rw [theta_frobeniusPerm_apply, conjugate_apply (E := E), conjugate_apply (E := E),
    theta_frobeniusPerm_apply]

variable {K p} {Φ : (E →+* ℝ) → (K →+* ℂ)} (hΦ : IsCMSection E K Φ)

/-- Geometric Frobenius as a conjugation-compatible permutation of the CM factor
indices of `Φ`. -/
def frobeniusCMPerm (θ : ℂ →+* PadicAlgCl p) : CMPerm (E →+* ℝ) :=
  CMPerm.ofEmbeddingPerm hΦ (frobeniusPerm K p θ)
    (frobeniusPerm_conjugate (E := E) (K := K) (p := p) θ)

end Frobenius

/-! ### The local degree of the reflex field -/

section ReflexDegree

variable {K : Type v} [Field K] [NumberField K]

theorem exists_pow_preserves (F : Equiv.Perm (K →+* ℂ)) (h : (K →+* ℂ) → ℕ) :
    ∃ j, 0 < j ∧ ∀ i, h ((F ^ j) i) = h i :=
  ⟨orderOf F, orderOf_pos F, fun i => by rw [pow_orderOf_eq_one]; rfl⟩

/-- The least positive power of a permutation `F` of the complex embeddings that
preserves the function `h`. For `F = frobeniusPerm K p θ` and Kottwitz's function
`h = (i ↦ n(i))`, this is the local degree `[E_v : ℚ_p]` of the reflex field at the
place `v` induced by `θ` when `E_v / ℚ_p` is unramified (see the Markdown). -/
def hodgeOrbitDegree (F : Equiv.Perm (K →+* ℂ)) (h : (K →+* ℂ) → ℕ) : ℕ :=
  Nat.find (exists_pow_preserves F h)

theorem hodgeOrbitDegree_pos (F : Equiv.Perm (K →+* ℂ)) (h : (K →+* ℂ) → ℕ) :
    0 < hodgeOrbitDegree F h := by
  classical
  exact (Nat.find_spec (exists_pow_preserves F h)).1

theorem hodgeOrbitDegree_preserves (F : Equiv.Perm (K →+* ℂ)) (h : (K →+* ℂ) → ℕ)
    (i : K →+* ℂ) : h ((F ^ hodgeOrbitDegree F h) i) = h i := by
  classical
  exact (Nat.find_spec (exists_pow_preserves F h)).2 i

end ReflexDegree

end Langlands.Shimura.KottwitzDual
