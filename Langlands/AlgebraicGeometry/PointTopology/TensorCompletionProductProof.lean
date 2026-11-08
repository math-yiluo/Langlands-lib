import Langlands.AlgebraicGeometry.PointTopology.HenselianValuedFieldPropertiesStatement
import Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedFieldProof
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The completion tensored with a finite separable extension

Let `K` be a nontrivially normed field with absolute value `v = ‖·‖`, completion `K_v`, and let
`L/K` be finite separable. Then `K_v ⊗_K L` is the product of the completions `L_w` over the
finitely many absolute values `w` of `L` lying over `v`.

`K_v ⊗_K L` is finite étale over `K_v`, so it is a finite product of fields `E_i`, each finite over
the complete field `K_v`. Each `E_i` carries a unique absolute value extending that of `K_v`; its
restriction to `L` is an absolute value `w_i` over `v`.

* Every `w` over `v` is some `w_i`: the map `K_v ⊗_K L → L_w` factors through one `E_i`, and the
  absolute value of `L_w` restricts on `E_i` to the unique one.
* `i ↦ w_i` is injective: an idempotent separating `E_i` from `E_k` is approximated by an element
  of `L`, whose absolute values under `w_i` and `w_k` then differ.
* `E_i → L_{w_i}` is onto: its image is a finite-dimensional, hence closed, `K_v`-subspace that
  contains the dense image of `L`.
-/

noncomputable section

universe u

open Polynomial
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

namespace TensorCompletionProduct

variable (K : Type u) [NontriviallyNormedField K]

local notation "v" => NormedField.toAbsoluteValue K
local notation "Kv" => AbsoluteValue.Completion (NormedField.toAbsoluteValue K)

/-- The completion of `K` at its norm is a nontrivially normed field. -/
@[instance_reducible]
def completionNormedField : NontriviallyNormedField Kv :=
  { (inferInstance : NormedField Kv) with
    non_trivial := by
      obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
      refine ⟨((WithAbs.toAbs v x : WithAbs v) : Kv), ?_⟩
      rw [UniformSpace.Completion.norm_coe, WithAbs.norm_toAbs_eq]
      exact hx }

variable {K}

theorem norm_algebraMap (x : K) : ‖algebraMap K Kv x‖ = ‖x‖ := by
  change ‖((WithAbs.toAbs v x : WithAbs v) : Kv)‖ = ‖x‖
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_toAbs_eq]
  rfl

theorem denseRange_algebraMap : DenseRange (algebraMap K Kv) := by
  have : (algebraMap K Kv : K → Kv) =
      ((↑) : WithAbs v → Kv) ∘ WithAbs.toAbs v := rfl
  rw [this]
  exact UniformSpace.Completion.denseRange_coe.comp (WithAbs.toAbs_surjective v).denseRange
    (UniformSpace.Completion.continuous_coe _)

/-- An algebra map out of a finite product of fields into a field factors through one
factor. -/
theorem exists_factor {F : Type*} [Field F] {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, Field (E i)] [∀ i, Algebra F (E i)] {D : Type*} [Field D] [Algebra F D]
    (ψ : (∀ i, E i) →ₐ[F] D) : ∃ i, ∃ μ : E i →ₐ[F] D, ∀ x, ψ x = μ (x i) := by
  classical
  have hid : ∀ i, ψ (Pi.single i 1) = 0 ∨ ψ (Pi.single i 1) = 1 := fun i =>
    IsIdempotentElem.iff_eq_zero_or_one.mp
      (by rw [IsIdempotentElem, ← map_mul, ← Pi.single_mul, mul_one])
  obtain ⟨i, hi⟩ : ∃ i, ψ (Pi.single i 1) = 1 := by
    by_contra h
    push Not at h
    have h0 : ∀ i, ψ (Pi.single i 1) = 0 := fun i => (hid i).resolve_right (h i)
    have := congrArg ψ (Finset.univ_sum_single (fun _ => (1 : _) : ∀ i, E i))
    rw [map_sum, Finset.sum_eq_zero fun i _ => h0 i] at this
    exact zero_ne_one (this.trans (map_one ψ))
  have hmul : ∀ x : ∀ i, E i, x * Pi.single i 1 = Pi.single i (x i) := fun x => by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  let μ : E i →ₐ[F] D :=
    { toFun := fun y => ψ (Pi.single i y)
      map_one' := hi
      map_mul' := fun y z => by rw [Pi.single_mul, map_mul]
      map_zero' := by rw [Pi.single_zero, map_zero]
      map_add' := fun y z => by rw [Pi.single_add, map_add]
      commutes' := fun c => by
        rw [show Pi.single i (algebraMap F (E i) c) = algebraMap F (∀ i, E i) c * Pi.single i 1
          by rw [hmul]; rfl, map_mul, AlgHom.commutes, hi, mul_one] }
  refine ⟨i, μ, fun x => ?_⟩
  change ψ x = ψ (Pi.single i (x i))
  rw [← hmul, map_mul, hi, mul_one]

/-- The pullback of an absolute value along a field map. -/
def pullback {R M : Type*} [Field R] [Field M] (u : AbsoluteValue M ℝ) (f : R →+* M) :
    AbsoluteValue R ℝ where
  toFun x := u (f x)
  map_mul' x y := by simp
  nonneg' x := u.nonneg _
  eq_zero' x := by simp
  add_le' x y := by simpa using u.add_le _ _

@[simp] theorem pullback_apply {R M : Type*} [Field R] [Field M] (u : AbsoluteValue M ℝ)
    (f : R →+* M) (x : R) : pullback u f x = u (f x) := rfl

section Over

variable {L : Type u} [Field L] [Algebra K L] (w : AbsoluteValue L ℝ)

/-- The inclusion of `L` in its completion at `w`. -/
def coeL : L →ₐ[K] w.Completion :=
  { (UniformSpace.Completion.coeRingHom : WithAbs w →+* w.Completion).comp
      (WithAbs.equiv w).symm.toRingHom with
    commutes' := fun _ => rfl }

theorem norm_coeL (x : L) : ‖coeL (K := K) w x‖ = w x := by
  change ‖((WithAbs.toAbs w x : WithAbs w) : w.Completion)‖ = w x
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_toAbs_eq]

theorem denseRange_coeL : DenseRange (coeL (K := K) w) := by
  have : (coeL (K := K) w : L → w.Completion) = ((↑) : WithAbs w → w.Completion) ∘ WithAbs.toAbs w := rfl
  rw [this]
  exact UniformSpace.Completion.denseRange_coe.comp (WithAbs.toAbs_surjective w).denseRange
    (UniformSpace.Completion.continuous_coe _)

theorem norm_algebraMap_over [w.LiesOver (NormedField.toAbsoluteValue K)] (c : Kv) :
    letI := AbsoluteValue.Completion.algebraOfLiesOver v w
    ‖algebraMap Kv w.Completion c‖ = ‖c‖ := by
  let := AbsoluteValue.Completion.algebraOfLiesOver v w
  exact (UniformSpace.Completion.isometry_mapRingHom (WithAbs.isometry_map v w)).norm_map_of_map_zero
    (map_zero _) c

end Over

section Main

variable {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **The completion tensored with a finite separable extension is the product of the
completions over the absolute values lying over `v`.** -/
theorem main : Finite {w : AbsoluteValue L ℝ // w.LiesOver v} ∧
    letI (w : {w : AbsoluteValue L ℝ // w.LiesOver v}) : Algebra Kv w.1.Completion :=
      @AbsoluteValue.Completion.algebraOfLiesOver K _ v L _ _ w.1 w.2
    Nonempty (Kv ⊗[K] L ≃ₐ[Kv] ∀ w : {w : AbsoluteValue L ℝ // w.LiesOver v}, w.1.Completion) := by
  classical
  let _ := completionNormedField K
  have : Algebra.Etale K L :=
    ⟨Algebra.FormallyEtale.of_isSeparable K L, Algebra.FinitePresentation.of_finiteType.mp
      inferInstance⟩
  obtain ⟨I, _, E, _, _, e, hE⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod Kv (Kv ⊗[K] L)).mp inferInstance
  have : Fintype I := Fintype.ofFinite I
  let _ : ∀ i, Algebra K (E i) := fun i =>
    ((algebraMap Kv (E i)).comp (algebraMap K Kv)).toAlgebra
  have : ∀ i, IsScalarTower K Kv (E i) := fun i => IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hext : ∀ i, ∃! a : AbsoluteValue (E i) ℝ, ∀ c : Kv, a (algebraMap Kv (E i) c) = ‖c‖ := by
    intro i
    have := (hE i).1
    have : Algebra.IsAlgebraic Kv (E i) := Algebra.IsAlgebraic.of_finite _ _
    exact completeHenselianValuedField Kv (E i)
  choose a ha hauniq using hext
  let π : ∀ i, Kv ⊗[K] L →ₐ[Kv] E i := fun i => (Pi.evalAlgHom Kv E i).comp e.toAlgHom
  let ι : ∀ i, L →ₐ[K] E i := fun i =>
    ((π i).restrictScalars K).comp Algebra.TensorProduct.includeRight
  let w : I → AbsoluteValue L ℝ := fun i => pullback (a i) (ι i).toRingHom
  have hwapp : ∀ i x, w i x = a i (ι i x) := fun _ _ => rfl
  have hw : ∀ i, (w i).LiesOver v := fun i => ⟨by
    ext x
    change a i (ι i (algebraMap K L x)) = ‖x‖
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K Kv (E i), ha, norm_algebraMap]⟩
  -- every absolute value over `v` comes from a factor
  have hfac : ∀ (w' : AbsoluteValue L ℝ) (hw' : w'.LiesOver v),
      letI := @AbsoluteValue.Completion.algebraOfLiesOver K _ v L _ _ w' hw'
      ∃ i, ∃ μ : E i →ₐ[Kv] w'.Completion,
        (∀ x : L, μ (ι i x) = coeL (K := K) w' x) ∧ w' = w i := by
    intro w' hw'
    let := @AbsoluteValue.Completion.algebraOfLiesOver K _ v L _ _ w' hw'
    let Ψ : Kv ⊗[K] L →ₐ[Kv] w'.Completion :=
      Algebra.TensorProduct.lift (Algebra.ofId Kv _) (coeL (K := K) w') (fun _ _ => Commute.all _ _)
    obtain ⟨i, μ, hμ⟩ := exists_factor (Ψ.comp e.symm.toAlgHom)
    have hμι : ∀ x : L, μ (ι i x) = coeL (K := K) w' x := by
      intro x
      have h1 := hμ (e (1 ⊗ₜ x))
      change Ψ (e.symm (e (1 ⊗ₜ x))) = μ (ι i x) at h1
      rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul] at h1
      exact h1.symm
    refine ⟨i, μ, hμι, ?_⟩
    have hb : pullback (NormedField.toAbsoluteValue w'.Completion) μ.toRingHom = a i :=
      hauniq i _ fun c => by
        change ‖μ (algebraMap Kv (E i) c)‖ = ‖c‖
        rw [AlgHom.commutes]
        exact @norm_algebraMap_over K _ L _ _ w' hw' c
    ext x
    rw [hwapp, ← hb, pullback_apply]
    change w' x = ‖μ (ι i x)‖
    rw [hμι, norm_coeL]
  -- distinct factors give distinct absolute values
  have hinj : Function.Injective w := by
    intro i k hik
    by_contra hne
    let ε : Kv ⊗[K] L := e.symm (Pi.single i 1)
    have hεi : π i ε = 1 := by simp [π, ε]
    have hεk : π k ε = 0 := by simp [π, ε, Ne.symm hne]
    let b := Module.Free.chooseBasis K L
    let B := Algebra.TensorProduct.basis Kv b
    set S : ℝ := ∑ m, w i (b m) with hSdef
    have hS : 0 ≤ S := Finset.sum_nonneg fun m _ => (w i).nonneg _
    set δ : ℝ := 1 / (4 * (S + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    have happrox : ∀ m, ∃ c : K, ‖algebraMap K Kv c - B.repr ε m‖ < δ := fun m => by
      obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp denseRange_algebraMap (B.repr ε m) δ hδ
      exact ⟨c, by rw [← dist_eq_norm, dist_comm]; exact hc⟩
    choose c hc using happrox
    let y : L := ∑ m, c m • b m
    have hest : ∀ j, a j (ι j y - π j ε) ≤ δ * ∑ m, w j (b m) := by
      intro j
      have hε : π j ε = ∑ m, algebraMap Kv (E j) (B.repr ε m) * ι j (b m) := by
        conv_lhs => rw [← B.sum_repr ε]
        rw [map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_smul, Algebra.TensorProduct.basis_apply, Algebra.smul_def]
        rfl
      have hy : ι j y = ∑ m, algebraMap Kv (E j) (algebraMap K Kv (c m)) * ι j (b m) := by
        simp only [y, map_sum, Algebra.smul_def]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← IsScalarTower.algebraMap_apply, map_mul, AlgHom.commutes]
      rw [hy, hε, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine ((a j).sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [← sub_mul, ← map_sub, map_mul, ha, hwapp]
      exact mul_le_mul_of_nonneg_right (hc m).le ((a j).nonneg _)
    have hSk : ∑ m, w k (b m) = S := by rw [hSdef, hik]
    have h1 : 1 ≤ a i (ι i y) + δ * S := by
      have := (a i).add_le (ι i y) (π i ε - ι i y)
      rw [add_sub_cancel, hεi, map_one, AbsoluteValue.map_sub] at this
      have h' := hest i
      rw [hεi, ← hSdef] at h'
      linarith
    have h2 : a k (ι k y) ≤ δ * S := by
      have := hest k
      rwa [hεk, sub_zero, hSk] at this
    have h3 : a i (ι i y) = a k (ι k y) := by
      rw [← hwapp, ← hwapp, hik]
    have h4 : δ * S < 1 / 2 := by
      rw [hδdef, div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  -- the bijection between factors and absolute values over `v`
  let σ : I → {w : AbsoluteValue L ℝ // w.LiesOver v} := fun i => ⟨w i, hw i⟩
  have hσinj : Function.Injective σ := fun i k h => hinj (congrArg Subtype.val h)
  have hσsurj : Function.Surjective σ := by
    rintro ⟨w', hw'⟩
    obtain ⟨i, -, -, h⟩ := hfac w' hw'
    exact ⟨i, Subtype.ext h.symm⟩
  refine ⟨Finite.of_surjective σ hσsurj, ?_⟩
  let _ : ∀ w' : {w : AbsoluteValue L ℝ // w.LiesOver v}, Algebra Kv w'.1.Completion :=
    fun w' => @AbsoluteValue.Completion.algebraOfLiesOver K _ v L _ _ w'.1 w'.2
  -- each factor is the completion
  have hT : ∀ i, Nonempty (E i ≃ₐ[Kv] (σ i).1.Completion) := by
    intro i
    obtain ⟨i', μ, hμι, hi'⟩ := hfac (w i) (hw i)
    have : i' = i := hinj hi'.symm
    subst this
    let := @AbsoluteValue.Completion.algebraOfLiesOver K _ v L _ _ (w i') (hw i')
    have := (hE i').1
    have hsurj : Function.Surjective μ := by
      let R := LinearMap.range μ.toLinearMap
      have hclosed : IsClosed (R : Set (w i').Completion) := Submodule.closed_of_finiteDimensional R
      have hsub : Set.range (coeL (K := K) (w i')) ⊆ (R : Set (w i').Completion) := by
        rintro _ ⟨x, rfl⟩
        exact LinearMap.mem_range.mpr ⟨ι i' x, hμι x⟩
      intro z
      have hz := closure_minimal hsub hclosed (denseRange_coeL (K := K) (w i') z)
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hz
      exact ⟨y, hy⟩
    exact ⟨AlgEquiv.ofBijective μ ⟨μ.injective, hsurj⟩⟩
  exact ⟨e.trans ((AlgEquiv.piCongrRight fun i => (hT i).some).trans
    (AlgEquiv.piCongrLeft Kv (fun w : {w : AbsoluteValue L ℝ // w.LiesOver v} => w.1.Completion)
      (Equiv.ofBijective σ ⟨hσinj, hσsurj⟩)))⟩

end Main

end TensorCompletionProduct

/-- **The completion tensored with a finite separable extension** (Conrad, printed p.14): there are
finitely many absolute values of `L` over the norm of `K`, and `K_v ⊗_K L` is the product of the
corresponding completions. -/
theorem tensorCompletionProduct : TensorCompletionProductStatement.{u} := by
  intro K _ L _ _ _ _
  exact TensorCompletionProduct.main (K := K) (L := L)

end Langlands.AlgebraicGeometry.PointTopology
