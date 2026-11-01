import Langlands.Representation.Derivative.MirabolicCharacter
import Langlands.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Parabolic.QuotientCompactProof

/-!
# Successor and radical lemmas for left mixed products

Auxiliary results for comparing the case (II) mixed products of Bernstein-Zelevinsky
§4.12(II) with the plus functors on mirabolic groups.

* `leftSuccessor` and `leftRadical` restrict the successor embedding `P_(k+n+1) → P_(k+n+2)`
  and the actual radical of `P_(k+n+1)` to the case (II) subgroups, with their block
  projections.
* `determinantNorm_leftSubgroup`, `determinantNorm_radical'` and `determinantNorm_successor`
  compute normalized determinant norms.
* `compactSpace_leftQuotient`: the coset space `leftSubgroup k n \ P_(k+n+1)` is compact.
* `isCompact_quotientSupport_of_covariant`: a covariant function fixed by an open subgroup
  under right translation has compact projected support when the coset space is compact.
* `eq_zero_of_forall_dual_rTensor`: a complex tensor killed by every functional on the left
  factor is zero.
-/

noncomputable section

namespace Langlands.GeneralLinear.Mirabolic.MixedProduct

universe u

variable {R : Type u} [CommRing R] {k n : ℕ}

theorem leftIndex_inr_castSucc (i : Fin (n + 1)) :
    leftIndex k (n + 1) (Sum.inr i.castSucc) = (leftIndex k n (Sum.inr i)).castSucc :=
  Fin.ext (by simp)

theorem leftIndex_inl_castSucc (j : Fin k) :
    leftIndex k (n + 1) (Sum.inl j) = (leftIndex k n (Sum.inl j)).castSucc :=
  Fin.ext (by simp)

theorem leftIndex_inl_ne_last (j : Fin k) :
    leftIndex k n (Sum.inl j) ≠ Fin.last (k + n) := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- The successor embedding maps the case (II) subgroup into the case (II) subgroup. -/
theorem successor_mem_leftSubgroup (h : leftSubgroup k n R) :
    successor (h : mirabolic (k + n) R) ∈ leftSubgroup k (n + 1) R := by
  rw [mem_leftSubgroup_iff_entry]
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [leftIndex_last]
    have hlast := (successor (h : mirabolic (k + n) R)).property (leftIndex k (n + 1) (Sum.inl j))
    exact hlast.trans (ite_eq_right (leftIndex_inl_ne_last (n := n + 1) j))
  · rw [leftIndex_inr_castSucc, leftIndex_inl_castSucc, successor_first]
    exact (mem_leftSubgroup_iff_entry _).mp h.property i j

/-- The successor embedding restricted to the case (II) subgroups. -/
def leftSuccessor : leftSubgroup k n R →* leftSubgroup k (n + 1) R :=
  (successor.comp (leftSubgroup k n R).subtype).codRestrict _ successor_mem_leftSubgroup

@[simp] theorem leftSuccessor_val (h : leftSubgroup k n R) :
    ((leftSuccessor h : leftSubgroup k (n + 1) R) : mirabolic (k + (n + 1)) R) =
      successor (h : mirabolic (k + n) R) := rfl

theorem leftIndex_inr_eq_last_iff (j : Fin (n + 1)) :
    leftIndex k n (Sum.inr j) = Fin.last (k + n) ↔ j = Fin.last n := by
  rw [← leftIndex_last (k := k) (r := n), Equiv.apply_eq_iff_eq, Sum.inr.injEq]

/-- `leftProjection (successor h) = (a, successor p)` for `leftProjection h = (a, p)`. -/
theorem leftProjection_leftSuccessor (h : leftSubgroup k n R) :
    leftProjection (leftSuccessor h) =
      ((leftProjection h).1, successor (leftProjection h).2) := by
  apply Prod.ext
  · apply Units.ext
    ext i j
    change (successor (h : mirabolic (k + n) R)).val.val (leftIndex k (n + 1) (Sum.inl i))
      (leftIndex k (n + 1) (Sum.inl j)) = _
    rw [leftIndex_inl_castSucc, leftIndex_inl_castSucc, successor_first]
    rfl
  · apply Subtype.ext
    apply Units.ext
    ext i j
    change (successor (h : mirabolic (k + n) R)).val.val (leftIndex k (n + 1) (Sum.inr i))
      (leftIndex k (n + 1) (Sum.inr j)) = (successor (leftProjection h).2).val.val i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [leftIndex_last]
      have h1 := (successor (h : mirabolic (k + n) R)).property (leftIndex k (n + 1) (Sum.inr j))
      have h2 := (successor (leftProjection h).2).property j
      refine h1.trans (h2.trans ?_).symm
      exact if_congr (leftIndex_inr_eq_last_iff (k := k) (n := n + 1) j).symm rfl rfl
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [leftIndex_last, leftIndex_inr_castSucc]
        exact (successor_last _ _).trans (successor_last _ _).symm
      · rw [leftIndex_inr_castSucc, leftIndex_inr_castSucc, successor_first, successor_first]
        rfl

theorem leftIndex_inr_ne_inl (i : Fin (n + 1)) (j : Fin k) :
    leftIndex k n (Sum.inr i) ≠ leftIndex k n (Sum.inl j) := by
  rw [Ne, Equiv.apply_eq_iff_eq]
  exact Sum.inr_ne_inl

/-- The first `k` coordinates are columns of the actual radical. -/
theorem leftIndex_inl_eq_castSucc (j : Fin k) :
    leftIndex k n (Sum.inl j) = (⟨j.val, by omega⟩ : Fin (k + n)).castSucc :=
  Fin.ext (by simp)

/-- The actual radical of `P_(k+r+1)` lies in the case (II) subgroup. -/
theorem radical_mem_leftSubgroup (u : radical (k + n) R) :
    (u : mirabolic (k + n) R) ∈ leftSubgroup k n R := by
  rw [mem_leftSubgroup_iff_entry]
  intro i j
  have hu := u.property (leftIndex k n (Sum.inr i)) ⟨j.val, by omega⟩
  rw [← leftIndex_inl_eq_castSucc] at hu
  exact hu.trans (ite_eq_right (leftIndex_inr_ne_inl i j))

/-- The actual radical as a subgroup of the case (II) subgroup. -/
def leftRadical : radical (k + n) R →* leftSubgroup k n R :=
  ((radical (k + n) R).subtype).codRestrict _ radical_mem_leftSubgroup

@[simp] theorem leftRadical_val (u : radical (k + n) R) :
    ((leftRadical u : leftSubgroup k n R) : mirabolic (k + n) R) = u := rfl

theorem leftProjection_leftRadical_fst (u : radical (k + n) R) :
    (leftProjection (leftRadical u)).1 = 1 := by
  apply Units.ext
  ext i j
  change (u : mirabolic (k + n) R).val.val (leftIndex k n (Sum.inl i))
    (leftIndex k n (Sum.inl j)) = (1 : Matrix (Fin k) (Fin k) R) i j
  rw [leftIndex_inl_eq_castSucc (n := n) j, u.property, Matrix.one_apply,
    ← leftIndex_inl_eq_castSucc]
  simp only [Equiv.apply_eq_iff_eq, Sum.inl.injEq]

theorem leftProjection_leftRadical_snd_mem (u : radical (k + n) R) :
    (leftProjection (leftRadical u)).2 ∈ radical n R := by
  intro i j
  change (u : mirabolic (k + n) R).val.val (leftIndex k n (Sum.inr i))
    (leftIndex k n (Sum.inr j.castSucc)) = _
  have hj : leftIndex k n (Sum.inr j.castSucc) =
      (⟨k + j.val, by omega⟩ : Fin (k + n)).castSucc := Fin.ext (by simp)
  rw [hj, u.property, ← hj]
  simp only [Equiv.apply_eq_iff_eq, Sum.inr.injEq]

/-- The radical projection keeps the last radical coordinate, so it keeps `θ`. -/
theorem theta_leftProjection_leftRadical [TopologicalSpace R]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter R) (u : radical (k + (n + 1)) R) :
    Derivative.Mirabolic.theta ψ n
        ⟨(leftProjection (leftRadical u)).2, leftProjection_leftRadical_snd_mem u⟩ =
      Derivative.Mirabolic.theta ψ (k + n) u := by
  apply Units.ext
  rw [Derivative.Mirabolic.theta_apply, Derivative.Mirabolic.theta_apply]
  congr 1

/-- The determinant of a case (II) element is the product of its diagonal block determinants. -/
theorem det_leftSubgroup (g : leftSubgroup k n R) :
    (g : mirabolic (k + n) R).val.val.det =
      (leftProjection g).1.val.det * (leftProjection g).2.val.val.det := by
  conv_lhs => rw [← leftMatrix_parts g]
  change Matrix.det (Matrix.reindex (leftIndex k n) (leftIndex k n)
    (Matrix.fromBlocks (leftProjection g).1.val (leftOffDiagonal g) 0
      (leftProjection g).2.val.val)) = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

/-- Upper triangular Levi elements lie in the case (II) subgroup. -/
theorem levi_mem_leftSubgroup_of_isUpperTriangular {m : Langlands.GeneralLinear (k + n) R}
    (hm : m.val.IsUpperTriangular) : levi m ∈ leftSubgroup k n R := by
  rw [mem_leftSubgroup_iff_entry]
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [leftIndex_last, levi_bottom]
    exact ite_eq_right (leftIndex_inl_ne_last j)
  · have hi : leftIndex k n (Sum.inr i.castSucc) =
        (⟨k + i.val, by omega⟩ : Fin (k + n)).castSucc := Fin.ext (by simp)
    rw [hi, leftIndex_inl_eq_castSucc, levi_first]
    exact hm (Fin.mk_lt_mk.mpr (by omega))

end Langlands.GeneralLinear.Mirabolic.MixedProduct

namespace Langlands.PadicField.TopologicalData

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {k n : ℕ}

/-- `ν(h) = ν(a) ν(p)` for `h ∈ leftSubgroup` with diagonal blocks `(a, p)`. -/
theorem determinantNorm_leftSubgroup (g : leftSubgroup k n F.Carrier) :
    T.determinantNorm (k + n + 1) (g : mirabolic (k + n) F.Carrier).val =
      T.determinantNorm k (leftProjection g).1 *
        T.determinantNorm (n + 1) (leftProjection g).2.val := by
  change T.normalizedAbsUnits (determinant _) =
    T.normalizedAbsUnits (determinant _) * T.normalizedAbsUnits (determinant _)
  rw [← map_mul]
  congr 1
  exact Units.ext (det_leftSubgroup g)

/-- Every coset `leftSubgroup * x` meets the Levi image of the integral group. -/
theorem quotientMap_leftSubgroup_image_levi_integralRange (k n : ℕ) :
    letI := T.valuativeRel
    Induction.quotientMap (leftSubgroup k n F.Carrier) ''
      (levi '' (Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) (k + n) :
        Set (GeneralLinear (k + n) F.Carrier))) = Set.univ := by
  let := T.valuativeRel
  refine Set.eq_univ_of_forall fun x => ?_
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨κ, hκ, hup⟩ := Iwasawa.exists_mul_upperTriangular
      (ValuativeRel.valuation F.Carrier) (k + n) (projection g)
    refine ⟨levi κ⁻¹, ⟨κ⁻¹, inv_mem hκ, rfl⟩, Quotient.sound ?_⟩
    change QuotientGroup.rightRel _ (levi κ⁻¹) g
    rw [QuotientGroup.rightRel_apply, map_inv, inv_inv]
    rw [eq_radicalElement_mul_levi g, mul_assoc, ← map_mul]
    exact mul_mem (radical_mem_leftSubgroup _) (levi_mem_leftSubgroup_of_isUpperTriangular hup)

/-- The coset space `leftSubgroup k n \ P_(k+n+1)` is compact. -/
theorem compactSpace_leftQuotient (k n : ℕ) :
    letI := T.topology
    CompactSpace (Induction.LeftQuotient (leftSubgroup k n F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  refine ⟨?_⟩
  rw [← T.quotientMap_leftSubgroup_image_levi_integralRange k n]
  exact ((Parabolic.isCompact_integralRange T (k + n)).image continuous_levi).image
    continuous_quotient_mk'

end Langlands.PadicField.TopologicalData

/-! ## Closed and compact projected supports -/

namespace Langlands.Induction

universe uR uG uW

variable {R : Type uR} {G : Type uG} {V : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

/-- A covariant function with one open subgroup of right stabilizers has closed projected
support. -/
theorem isClosed_quotientSupport_of_covariant (H : Subgroup G) (σ : Representation R H V)
    (f : G → V) (hcov : ∀ (h : H) (x : G), f ((h : G) * x) = σ h (f x))
    (K : OpenSubgroup G) (hK : ∀ (u : K) (x : G), f (x * (u : G)) = f x) :
    IsClosed (quotientSupport H f) := by
  have hlc : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro x
    refine ⟨(fun u => x * u) '' (K : Set G), isOpenMap_mul_left x _ K.isOpen,
      ⟨1, K.one_mem, mul_one x⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hK ⟨u, hu⟩ x
  have hpre : quotientMap H ⁻¹' quotientSupport H f = Function.support f := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩ hx
      have hh : y * x⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact hxy.symm)
      have heq := hcov ⟨y * x⁻¹, hh⟩ x
      rw [hx, map_zero, inv_mul_cancel_right] at heq
      exact hy heq
    · intro hx
      exact ⟨x, hx, rfl⟩
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel H)).isCoinducing.isClosed_preimage.mp
  change IsClosed (quotientMap H ⁻¹' quotientSupport H f)
  rw [hpre]
  exact (hlc.isOpen_fiber 0).isClosed_compl

/-- With a compact coset space, such a function has compact projected support. -/
theorem isCompact_quotientSupport_of_covariant (H : Subgroup G)
    [CompactSpace (LeftQuotient H)] (σ : Representation R H V)
    (f : G → V) (hcov : ∀ (h : H) (x : G), f ((h : G) * x) = σ h (f x))
    (K : OpenSubgroup G) (hK : ∀ (u : K) (x : G), f (x * (u : G)) = f x) :
    IsCompact (quotientSupport H f) :=
  (isClosed_quotientSupport_of_covariant H σ f hcov K hK).isCompact

end Langlands.Induction

/-! ## Vanishing of tensors -/

namespace Langlands.MixedProductTensor

open scoped TensorProduct

universe uX uY

/-- Over `ℂ`, a tensor vanishes once every functional on the left factor kills it. -/
theorem eq_zero_of_forall_dual_rTensor {V : Type uX} {M : Type uY} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup M] [Module ℂ M] (t : V ⊗[ℂ] M)
    (h : ∀ g : Module.Dual ℂ V, TensorProduct.lid ℂ M (g.rTensor M t) = 0) : t = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ V
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply, h, map_zero, Finsupp.coe_zero, Pi.zero_apply]

/-- Functionals on the left factor commute with linear maps on the right factor. -/
theorem lid_rTensor_lTensor {V : Type uX} {M : Type uY} {N : Type*} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (g : Module.Dual ℂ V) (e : M →ₗ[ℂ] N) (t : V ⊗[ℂ] M) :
    TensorProduct.lid ℂ N (g.rTensor N (e.lTensor V t)) =
      e (TensorProduct.lid ℂ M (g.rTensor M t)) := by
  induction t with
  | tmul v m => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']

end Langlands.MixedProductTensor

/-! ## Determinants -/

namespace Langlands.PadicField.TopologicalData

open GeneralLinear GeneralLinear.Mirabolic

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Radical elements have determinant one. -/
theorem det_radical {n : ℕ} (u : radical n F.Carrier) :
    (u : mirabolic n F.Carrier).val.val.det = 1 := by
  have hu : (u : mirabolic n F.Carrier).val ∈ GeneralLinear.upperUnipotent (n + 1) F.Carrier :=
    radical_le_upperUnipotent u.property
  change (u : mirabolic n F.Carrier).val.val.det = 1
  rw [Matrix.det_of_isUpperTriangular hu.1]
  exact Finset.prod_eq_one fun i _ => hu.2 i

/-- Radical elements have normalized determinant norm one. -/
theorem determinantNorm_radical' {n : ℕ} (u : radical n F.Carrier) :
    T.determinantNorm (n + 1) (u : mirabolic n F.Carrier).val = 1 := by
  change T.normalizedAbsUnits (determinant _) = 1
  rw [show determinant (u : mirabolic n F.Carrier).val = 1 from Units.ext (det_radical u),
    map_one]

/-- The successor embedding keeps the normalized determinant norm. -/
theorem determinantNorm_successor {n : ℕ} (h : mirabolic n F.Carrier) :
    T.determinantNorm (n + 1 + 1) (successor h).val = T.determinantNorm (n + 1) h.val := by
  have hdet : determinant (successor h).val = determinant h.val := by
    apply Units.ext
    change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks h.val.val 0 0 (1 : Langlands.GeneralLinear 1 F.Carrier).val)) =
        Matrix.det h.val.val
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Units.val_one, Matrix.det_one,
      mul_one]
  change T.normalizedAbsUnits (determinant (successor h).val) =
    T.normalizedAbsUnits (determinant h.val)
  rw [hdet]

end Langlands.PadicField.TopologicalData
