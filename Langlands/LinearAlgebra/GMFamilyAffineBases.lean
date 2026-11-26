import Langlands.LinearAlgebra.GMFamilyGramVolume
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic

/-! # Basis coefficients for affine intersections of half-spaces -/

noncomputable section

open scoped RealInnerProductSpace Matrix
open Classical

namespace Langlands.GMFamily

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gram volume detects linear independence. -/
theorem gramVolume_ne_zero_iff {ι : Type*} [Fintype ι] (v : ι → V) :
    gramVolume v ≠ 0 ↔ LinearIndependent ℝ v := by
  change Real.sqrt (Matrix.gram ℝ v).det ≠ 0 ↔ _
  rw [Real.sqrt_ne_zero'.eq, ← Matrix.det_gram_ne_zero_iff_linearIndependent]
  exact (Matrix.posSemidef_gram ℝ v).det_nonneg.lt_iff_ne.trans ne_comm

/-- For a square family, the Gram volume is the absolute determinant in orthonormal
coordinates. -/
theorem gramVolume_eq_abs_det_toMatrix {ι : Type*} [Fintype ι]
    (o : OrthonormalBasis ι ℝ V) (v : ι → V) :
    gramVolume v = |(o.toBasis.toMatrix v).det| := by
  change Real.sqrt (Matrix.gram ℝ v).det = _
  rw [Matrix.gram_eq_conjTranspose_mul o v]
  change Real.sqrt ((o.toBasis.toMatrix v)ᴴ * (o.toBasis.toMatrix v)).det = _
  rw [Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [RCLike.star_def, RCLike.conj_to_real, ← sq, Real.sqrt_sq_eq_abs]

variable [FiniteDimensional ℝ V]

/-- Basis coordinates compute the change of Gram volume by the absolute determinant. -/
theorem gramVolume_eq_mul_abs_det {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V) (v : ι → V) :
    gramVolume v = gramVolume b * |b.det v| := by
  let e : Fin (Module.finrank ℝ V) ≃ ι := Fintype.equivOfCardEq
    (by rw [Fintype.card_fin, Module.finrank_eq_card_basis b])
  let o := (stdOrthonormalBasis ℝ V).reindex e
  rw [gramVolume_eq_abs_det_toMatrix o, gramVolume_eq_abs_det_toMatrix o, Module.Basis.det_apply,
    ← abs_mul, ← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix]

/-- Replacing one vector of a basis changes the volume by the absolute value of the
corresponding coordinate of the replacement. -/
theorem gramVolume_update_basis_repr {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V) (i : ι) (w : V) :
    gramVolume (Function.update b i w) = gramVolume b * |b.repr w i| := by
  rw [gramVolume_eq_mul_abs_det b, Module.Basis.det_apply, Module.Basis.toMatrix_update,
    Module.Basis.toMatrix_self]
  rw [← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

namespace AffineBases

variable {ι : Type*} [Fintype ι] (v : ι → V)

/-- A basis of the ambient space presented as a subset of the indexed normals. -/
abbrev BasisIndex := {s : Finset ι //
  LinearIndependent ℝ (fun i : s => v i) ∧ Submodule.span ℝ (Set.range fun i : s => v i) = ⊤}

instance : Fintype (BasisIndex v) := by
  exact Fintype.ofFinite _

/-- The basis specified by a basis index. -/
def basis (B : BasisIndex v) : Module.Basis B.val ℝ V :=
  Module.Basis.mk B.property.1 B.property.2.ge

omit [FiniteDimensional ℝ V] [Fintype ι] in
@[simp] theorem basis_apply (B : BasisIndex v) (i : B.val) : basis v B i = v i := by
  rw [basis, Module.Basis.mk_apply]

/-- The unique functional giving the specified intercepts on the basis normals. -/
def vertex (B : BasisIndex v) : (ι → ℝ) →ₗ[ℝ] Module.Dual ℝ V where
  toFun b := (basis v B).constr ℝ (fun i => b i)
  map_add' x y := by rw [← map_add]; rfl
  map_smul' c x := by rw [← map_smul]; rfl

omit [FiniteDimensional ℝ V] [Fintype ι] in
@[simp] theorem vertex_apply_basis (B : BasisIndex v) (b : ι → ℝ) {i : ι} (hi : i ∈ B.val) :
    vertex v B b (v i) = b i := by
  rw [← basis_apply v B ⟨i, hi⟩]
  exact (basis v B).constr_basis ℝ _ _

/-- The slack of an inequality at the basis intersection. -/
def slack (B : BasisIndex v) (i : ι) : Module.Dual ℝ (ι → ℝ) where
  toFun b := vertex v B b (v i) - b i
  map_add' x y := by simp only [map_add, LinearMap.add_apply, Pi.add_apply]; ring
  map_smul' c x := by simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [FiniteDimensional ℝ V] [Fintype ι] in
@[simp] theorem slack_apply (B : BasisIndex v) (i : ι) (b : ι → ℝ) :
    slack v B i b = vertex v B b (v i) - b i := rfl

omit [FiniteDimensional ℝ V] [Fintype ι] in
@[simp] theorem slack_eq_zero_of_mem (B : BasisIndex v) {i : ι} (hi : i ∈ B.val) :
    slack v B i = 0 := by
  apply LinearMap.ext
  intro b
  rw [slack_apply, vertex_apply_basis v B b hi, sub_self, LinearMap.zero_apply]

/-- Feasibility off the arrangement of the nonzero slack forms. -/
def Feasible (B : BasisIndex v) (b : ι → ℝ) : Prop :=
  ∀ j, j ∉ B.val → 0 < slack v B j b

/-- The generic intercepts have no additional tight constraints at any basis intersection. -/
def Regular (b : ι → ℝ) : Prop :=
  ∀ (B : BasisIndex v) j, j ∉ B.val → slack v B j b ≠ 0

/-- The coefficient with a common denominator cleared. -/
def weight (ℓ : V →ₗ[ℝ] ℂ) (B : BasisIndex v) : ℂ :=
  (gramVolume (fun i : B.val => v i) : ℂ) * ∏ i ∈ Finset.univ \ B.val, ℓ (v i)

omit [FiniteDimensional ℝ V] [Fintype ι] in
private theorem vertex_congr_basis (B : BasisIndex v) {b c : ι → ℝ}
    (h : ∀ i ∈ B.val, b i = c i) : vertex v B b = vertex v B c :=
  congrArg ((basis v B).constr ℝ) (funext fun i => h i i.property)

omit [FiniteDimensional ℝ V] [Fintype ι] in
private theorem slack_single_of_notMem (B : BasisIndex v) {j k : ι} (hk : k ∉ B.val) :
    slack v B j ((Pi.single k (1 : ℝ) : ι → ℝ)) = - ((Pi.single k (1 : ℝ) : ι → ℝ) j) := by
  have h : vertex v B ((Pi.single k (1 : ℝ) : ι → ℝ)) = vertex v B 0 := by
    apply vertex_congr_basis
    intro i hi
    have hin : i ≠ k := fun h => hk (h ▸ hi)
    exact Pi.single_eq_of_ne hin _
  rw [slack_apply, h, map_zero, LinearMap.zero_apply, zero_sub]

omit [FiniteDimensional ℝ V] [Fintype ι] in
/-- A slack form for a constraint outside a basis is nonzero. -/
theorem slack_ne_zero_of_notMem (B : BasisIndex v) {j : ι} (hj : j ∉ B.val) :
    slack v B j ≠ 0 := by
  intro h
  have he := slack_single_of_notMem v B (j := j) hj
  simp [h] at he

omit [FiniteDimensional ℝ V] [Fintype ι] in
/-- The off-basis slack forms of a fixed basis are pairwise nonproportional. -/
theorem eq_of_slack_eq_smul (B : BasisIndex v) {j k : ι} (hj : j ∉ B.val) (_hk : k ∉ B.val)
    (a : ℝ) (h : slack v B j = a • slack v B k) : j = k := by
  by_contra hne
  have ht := congrArg (fun f : Module.Dual ℝ (ι → ℝ) => f ((Pi.single j (1 : ℝ) : ι → ℝ))) h
  rw [slack_single_of_notMem v B hj, LinearMap.smul_apply, slack_single_of_notMem v B hj,
    Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at ht
  simp at ht

omit [FiniteDimensional ℝ V] [Fintype ι] in
/-- A functional agreeing on all the basis normals is the specified vertex. -/
theorem vertex_eq_of_agrees (B : BasisIndex v) (b : ι → ℝ) (x : Module.Dual ℝ V)
    (hx : ∀ i ∈ B.val, x (v i) = b i) : vertex v B b = x := by
  apply (basis v B).ext
  intro i
  simp [vertex_apply_basis v B b i.property, hx _ i.property]

omit [FiniteDimensional ℝ V] [Fintype ι] in
/-- The number of normals in a basis is the ambient dimension. -/
theorem card_basisIndex (B : BasisIndex v) : B.val.card = Module.finrank ℝ V := by
  rw [Module.finrank_eq_card_basis (basis v B), Fintype.card_coe]

/-- Coefficients of the dependence obtained by adjoining `j` to a basis. The
coefficient of `j` is `-1`. -/
def dependence (B : BasisIndex v) (j k : ι) : ℝ :=
  if hk : k ∈ B.val then (basis v B).repr (v j) ⟨k, hk⟩ else if k = j then -1 else 0

omit [FiniteDimensional ℝ V] [Fintype ι] in
@[simp] theorem dependence_extra (B : BasisIndex v) {j : ι} (hj : j ∉ B.val) :
    dependence v B j j = -1 := by simp [dependence, hj]

omit [FiniteDimensional ℝ V] [Fintype ι] in
@[simp] theorem dependence_basis (B : BasisIndex v) (j : ι) (k : B.val) :
    dependence v B j k = (basis v B).repr (v j) k := by simp [dependence, k.property]

omit [FiniteDimensional ℝ V] [Fintype ι] in
/-- The adjoined normal is expanded in the basis by its coordinates. -/
theorem sum_dependence_smul_eq_zero (B : BasisIndex v) {j : ι} (hj : j ∉ B.val) :
    ∑ k ∈ insert j B.val, dependence v B j k • v k = 0 := by
  rw [Finset.sum_insert hj, dependence_extra v B hj, neg_one_smul]
  have hsum : ∑ k ∈ B.val, dependence v B j k • v k = v j := by
    rw [← Finset.sum_attach]
    simpa only [Finset.univ_eq_attach, dependence_basis, ← basis_apply v B] using
      (basis v B).sum_repr (v j)
  rw [hsum, neg_add_cancel]

omit [Fintype ι] in
private theorem exchange_equiv (B : Finset ι) {j k : ι} (hj : j ∉ B) (hk : k ∈ B) :
    ∃ e : (B : Type _) ≃ ((insert j B).erase k : Type _),
      ∀ i : B, (e i : ι) = if (i : ι) = k then j else i := by
  let f (i : B) : (insert j B).erase k :=
    ⟨if (i : ι) = k then j else i, by
      refine Finset.mem_erase.mpr ?_
      by_cases hi : (i : ι) = k
      · rw [ite_eq_left hi]
        exact ⟨fun h => hj (h.symm ▸ hk), Finset.mem_insert_self _ _⟩
      · simp [hi, i.property]⟩
  have hinj : Function.Injective f := by
    intro a b h
    have hc := congrArg Subtype.val h
    change (if (a : ι) = k then j else a) = (if (b : ι) = k then j else b) at hc
    apply Subtype.ext
    by_cases ha : (a : ι) = k <;> by_cases hb : (b : ι) = k
    · exact ha.trans hb.symm
    · have he : j = (b : ι) := by simpa [ha, hb] using hc
      exact (hj (he.symm ▸ b.property)).elim
    · have he : (a : ι) = j := by simpa [ha, hb] using hc
      exact (hj (he ▸ a.property)).elim
    · simpa [ha, hb] using hc
  have hsur : Function.Surjective f := by
    intro i
    obtain ⟨hik, hi⟩ := Finset.mem_erase.mp i.property
    rcases Finset.mem_insert.mp hi with he | hi'
    · refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
      simpa [f] using he.symm
    · refine ⟨⟨i, hi'⟩, Subtype.ext ?_⟩
      simp [f, hik]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsur⟩, fun _ => rfl⟩

omit [Fintype ι] in
/-- Deleting `k` from an augmented basis multiplies its volume by the absolute
coefficient of `k` in the chosen dependence. -/
theorem gramVolume_exchange (B : BasisIndex v) {j : ι} (hj : j ∉ B.val) {k : ι}
    (hk : k ∈ insert j B.val) :
    gramVolume (fun i : (insert j B.val).erase k => v i) =
      gramVolume (fun i : B.val => v i) * |dependence v B j k| := by
  rcases Finset.mem_insert.mp hk with rfl | hk'
  · rw [Finset.erase_insert hj, dependence_extra v B hj, abs_neg, abs_one, mul_one]
  · let : DecidableEq (B.val : Type _) := Classical.decEq _
    obtain ⟨e, he⟩ := exchange_equiv B.val hj hk'
    rw [← gramVolume_reindex e (fun i : (insert j B.val).erase k => v i)]
    have hfun : (fun i : (insert j B.val).erase k => v i) ∘ e =
        Function.update (basis v B) ⟨k, hk'⟩ (v j) := by
      ext i
      simp only [Function.comp_apply, he, Function.update_apply, basis_apply]
      by_cases hi : (i : ι) = k
      · simp [show i = ⟨k, hk'⟩ from Subtype.ext hi]
      · simp [hi, show i ≠ ⟨k, hk'⟩ from fun e' => hi (congrArg Subtype.val e')]
    rw [hfun, gramVolume_update_basis_repr (basis v B), dependence_basis v B j ⟨k, hk'⟩]
    congr 1
    exact congrArg gramVolume (funext (basis_apply v B))

omit [Fintype ι] in
/-- A deletion from an augmented basis is again a basis exactly when its dependence
coefficient is nonzero. -/
theorem exists_exchange_basis_iff (B : BasisIndex v) {j : ι} (hj : j ∉ B.val) {k : ι}
    (hk : k ∈ insert j B.val) :
    (∃ C : BasisIndex v, C.val = (insert j B.val).erase k) ↔ dependence v B j k ≠ 0 := by
  have hvol := gramVolume_exchange v B hj hk
  have hB : gramVolume (fun i : B.val => v i) ≠ 0 := (gramVolume_ne_zero_iff _).mpr B.property.1
  have hli : LinearIndependent ℝ (fun i : (insert j B.val).erase k => v i) ↔
      dependence v B j k ≠ 0 := by
    rw [← gramVolume_ne_zero_iff, hvol, mul_ne_zero_iff, abs_ne_zero, and_iff_right hB]
  constructor
  · rintro ⟨C, hC⟩
    apply hli.mp
    rw [← hC]
    exact C.property.1
  · intro hc
    refine ⟨⟨_, hli.mpr hc, ?_⟩, rfl⟩
    apply (hli.mpr hc).span_eq_top_of_card_eq_finrank'
    rw [Fintype.card_coe, Finset.card_erase_of_mem hk, Finset.card_insert_of_notMem hj,
      card_basisIndex v B]
    omega

omit [FiniteDimensional ℝ V] [Fintype ι] in
private theorem sum_slack_of_matches (B : BasisIndex v) {j : ι} (hj : j ∉ B.val) (b : ι → ℝ)
    (x : Module.Dual ℝ V) :
    ∑ k ∈ insert j B.val, dependence v B j k * (x (v k) - b k) =
      -(∑ k ∈ insert j B.val, dependence v B j k * b k) := by
  have h := congrArg x (sum_dependence_smul_eq_zero v B hj)
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h
  simp only [mul_sub, Finset.sum_sub_distrib, h, zero_sub]

omit [FiniteDimensional ℝ V] [Fintype ι] in
/-- The two vertex slack forms on exchanging a tight constraint are proportional,
with proportionality given by the dependence coefficient. -/
theorem slack_eq_neg_dependence_mul_slack_exchange (B : BasisIndex v) {j : ι} (hj : j ∉ B.val)
    {k : ι} (hk : k ∈ insert j B.val) (C : BasisIndex v)
    (hC : C.val = (insert j B.val).erase k) (b : ι → ℝ) :
    slack v B j b = -dependence v B j k * slack v C k b := by
  have hB := sum_slack_of_matches v B hj b (vertex v B b)
  have hC' := sum_slack_of_matches v B hj b (vertex v C b)
  rw [Finset.sum_eq_single j] at hB
  · rw [Finset.sum_eq_single k] at hC'
    · simp only [dependence_extra v B hj, neg_one_mul, ← slack_apply] at hB hC'
      linarith
    · intro i hi hik
      rw [vertex_apply_basis v C b (hC ▸ Finset.mem_erase.mpr ⟨hik, hi⟩), sub_self, mul_zero]
    · simp [hk]
  · intro i hi hij
    have hi' : i ∈ B.val := (Finset.mem_insert.mp hi).resolve_left hij
    rw [vertex_apply_basis v B b hi', sub_self, mul_zero]
  · simp

end AffineBases

end Langlands.GMFamily
