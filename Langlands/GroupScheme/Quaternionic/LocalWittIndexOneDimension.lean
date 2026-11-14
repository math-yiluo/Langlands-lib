import Langlands.GroupScheme.Quaternionic.HyperbolicBasis
import Langlands.GroupScheme.Quaternionic.IsometryWeights
import Langlands.GroupScheme.Quaternionic.QuaternionConjugation
import Langlands.LinearAlgebra.LocalQuadraticAnisotropicDimensionBound
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free

/-! # The dimension bound for local quaternionic forms of Witt index one -/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-- The original sesquilinear pairing, viewed as a bilinear map over its central
ground field. -/
def sesqFormBilinear (H : Matrix n n D) : (n → D) →ₗ[K] (n → D) →ₗ[K] D where
  toFun x :=
    { toFun := σ.sesqForm H x
      map_add' := σ.sesqForm_add_right H x
      map_smul' := fun c y => σ.sesqForm_smul_right_scalar H c x y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact σ.sesqForm_add_left H x y z
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    exact σ.sesqForm_smul_left_scalar H c x y

@[simp] theorem sesqFormBilinear_apply (H : Matrix n n D) (x y : n → D) :
    σ.sesqFormBilinear H x y = σ.sesqForm H x y := rfl

private theorem exists_alternatingCoordinate
    (hline : Module.finrank K σ.alternatingSubspace = 1) :
    ∃ f : D →ₗ[K] K, ∀ a ∈ σ.alternatingSubspace, f a = 0 → a = 0 := by
  have hne : σ.alternatingSubspace ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hline
    norm_num at hline
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hl0
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hline hl hl0
  refine ⟨f, fun a ha hfa => ?_⟩
  rw [hspan] at ha
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  have hc : c = 0 := by simpa [hf] using hfa
  simp [hc]

/-- A ground-field linear functional which is injective on the alternating line.
Its values away from that line are immaterial. -/
def alternatingCoordinate (hline : Module.finrank K σ.alternatingSubspace = 1) :
    D →ₗ[K] K :=
  Classical.choose (σ.exists_alternatingCoordinate hline)

theorem alternatingCoordinate_eq_zero_iff
    (hline : Module.finrank K σ.alternatingSubspace = 1)
    {a : D} (ha : a ∈ σ.alternatingSubspace) :
    σ.alternatingCoordinate hline a = 0 ↔ a = 0 :=
  ⟨Classical.choose_spec (σ.exists_alternatingCoordinate hline) a ha,
    fun h => by simp [h]⟩

/-- The actual scalar quadratic form obtained by taking a coordinate of the
self-pairing in the alternating line. -/
def traceValuedQuadraticForm (H : Matrix n n D)
    (hline : Module.finrank K σ.alternatingSubspace = 1) :
    QuadraticForm K (n → D) :=
  (σ.alternatingCoordinate hline).compQuadraticMap
    (LinearMap.BilinMap.toQuadraticMap (σ.sesqFormBilinear H))

@[simp] theorem traceValuedQuadraticForm_apply (H : Matrix n n D)
    (hline : Module.finrank K σ.alternatingSubspace = 1) (x : n → D) :
    σ.traceValuedQuadraticForm H hline x =
      σ.alternatingCoordinate hline (σ.sesqForm H x x) := rfl

theorem traceValuedQuadraticForm_eq_zero_iff [LinearOrder n] {H : Matrix n n D}
    (hH : σ.IsAntihermitian H) (hline : Module.finrank K σ.alternatingSubspace = 1)
    (x : n → D) :
    σ.traceValuedQuadraticForm H hline x = 0 ↔ σ.sesqForm H x x = 0 := by
  rw [traceValuedQuadraticForm_apply]
  exact σ.alternatingCoordinate_eq_zero_iff hline
    (sesqForm_self_mem_alternatingSubspace hH x)

/-- In Witt index one, a vector in the orthogonal complement of a hyperbolic
pair has zero self-pairing only when it is zero. -/
theorem eq_zero_of_ortho_of_wittIndex_one {H : Matrix n n D}
    (hH : σ.IsAntihermitian H) (hw : σ.wittIndex H = 1)
    {e f y : n → D} (hee : σ.sesqForm H e e = 0)
    (hef : σ.sesqForm H e f = 1) (hye : σ.sesqForm H y e = 0)
    (hyf : σ.sesqForm H y f = 0) (hyy : σ.sesqForm H y y = 0) : y = 0 := by
  by_contra hy0
  have hey : σ.sesqForm H e y = 0 := by
    rw [IsAntihermitian.sesqForm_swap σ hH, hye, map_zero, neg_zero]
  have hli : LinearIndependent D ![e, y] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (fun z => σ.sesqForm H z f) hab
    simp only [sesqForm_add_left, sesqForm_smul_left, hef, hyf, mul_one,
      mul_zero, add_zero, sesqForm_zero_left] at h1
    subst h1
    rw [zero_smul, zero_add] at hab
    exact ⟨rfl, (smul_eq_zero.mp hab).resolve_right hy0⟩
  have hW : σ.IsTotallyIsotropic H (Submodule.span D (Set.range ![e, y])) := by
    intro x hx z hz
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hx
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hz
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      sesqForm_add_left, sesqForm_add_right, sesqForm_smul_left, sesqForm_smul_right,
      hee, hey, hye, hyy]
    simp
  have h2 := finrank_le_wittIndex σ hW
  rw [finrank_span_eq_card hli, hw] at h2
  simp at h2

variable [FiniteDimensional K D] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A nondegenerate trace-valued antihermitian form over a four-dimensional
division algebra with three-dimensional symmetric subspace has at most three
variables if its Witt index is one, in every characteristic. -/
theorem card_le_three_of_wittIndex_one [LinearOrder n]
    (hdim : Module.finrank K D = 4)
    (hsym : Module.finrank K σ.symmetricSubspace = 3)
    {H : Matrix n n D} (hH : σ.IsAntihermitian H) (hu : IsUnit H)
    (hw : σ.wittIndex H = 1) : Fintype.card n ≤ 3 := by
  obtain ⟨e, he, hee⟩ := exists_isotropic_of_wittIndex_eq_one hw
  obtain ⟨f, hef, _hff⟩ := exists_hyperbolic_pair hH hu he hee
  let φ : (n → D) →ₗ[D] (Fin 2 → D) :=
    { toFun := fun x => ![σ.sesqForm H x e, σ.sesqForm H x f]
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp [sesqForm_add_left]
      map_smul' := fun a x => by
        ext i
        fin_cases i <;> simp [sesqForm_smul_left] }
  let W := (LinearMap.ker φ).restrictScalars K
  have hline : Module.finrank K σ.alternatingSubspace = 1 := by
    have hk : LinearMap.ker (LinearMap.id - σ.toLinearMap) = σ.symmetricSubspace := by
      ext a
      change a - σ a = 0 ↔ σ a - a = 0
      rw [sub_eq_zero, sub_eq_zero]
      exact eq_comm
    have h := (LinearMap.id - σ.toLinearMap).finrank_range_add_finrank_ker
    rw [hk, hsym, hdim] at h
    change Module.finrank K σ.alternatingSubspace + 3 = 4 at h
    omega
  let Q : QuadraticForm K W := (σ.traceValuedQuadraticForm H hline).comp W.subtype
  have hQ : Q.Anisotropic := by
    intro x hx
    apply Subtype.ext
    have hx0 : σ.sesqForm H x.val x.val = 0 :=
      (σ.traceValuedQuadraticForm_eq_zero_iff hH hline x.val).mp hx
    have hxφ : φ x.val = 0 := x.property
    have hxe : σ.sesqForm H x.val e = 0 := by
      simpa [φ] using congrFun hxφ 0
    have hxf : σ.sesqForm H x.val f = 0 := by
      simpa [φ] using congrFun hxφ 1
    exact σ.eq_zero_of_ortho_of_wittIndex_one hH hw hee hef hxe hxf hx0
  have hK : Module.finrank K W ≤ 4 :=
    Langlands.localQuadraticAnisotropicDimensionBound K W Q hQ
  have htower := Module.finrank_mul_finrank K D W
  rw [hdim] at htower
  have hD : Module.finrank D (LinearMap.ker φ) ≤ 1 := by
    have heq : Module.finrank D W = Module.finrank D (LinearMap.ker φ) :=
      (Submodule.restrictScalarsEquiv K D (n → D) (LinearMap.ker φ)).finrank_eq
    rw [heq] at htower
    omega
  have hsum := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank D (LinearMap.range φ) ≤ 2 := by
    simpa using Submodule.finrank_le (LinearMap.range φ)
  rw [Module.finrank_fintype_fun_eq_card] at hsum
  omega

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
