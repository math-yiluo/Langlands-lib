import Langlands.Representation.Archimedean.RealInductionStagesFamily
import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof

/-!
# Averaging linear maps between `O(r)`-finite functions over `O(r)`

For a linear map `A` from the `O(r)`-finite functions of the real standard module of `ds` to
those of `es`, the average `avg A f = ∫_{O(r)} R(k)⁻¹ A (R(k) f) dk` (normalized Haar measure,
pointwise integral) commutes exactly with right translation by `O(r)` (`avg_kRep`).

If `M` is a subspace of the target stable under `O(r)`, then

* `avg A f - c ∈ M` whenever `R(k)⁻¹ A (R(k) f) - c ∈ M` for all `k` (`avg_sub_mem`); in
  particular `avg A f - A f ∈ M` if `A` commutes with `O(r)` modulo `M`
  (`avg_sub_self_mem`);
* `R(X) avg A f - avg A (R(X) f) ∈ M` if `A` commutes with all right derivatives modulo `M`
  (`lie_avg_sub_mem`);

and an exactly `O(r)`-equivariant `B` satisfies `B ∘ avg A = avg (B ∘ A)` (`map_avg`).
-/

noncomputable section

open MeasureTheory
open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

namespace InductionStages

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] RealPrincipalSeriesDuality.measurableSpaceK

set_option backward.isDefEq.respectTransparency false

local instance borelSpaceK' (r : ℕ) : BorelSpace (unitaryCompact ℝ r) := ⟨rfl⟩

/-- The `O(r)`-finite functions of the real standard module of `ds` on `GL_r(ℝ)`. -/
abbrev KFin (r : ℕ) (ds : List RealBlock) : Submodule ℂ (Langlands.GeneralLinear r ℝ → ℂ) :=
  kFiniteFunctions (realStandardModule r ds) (unitaryCompact ℝ r)

/-- `O(r)` as a subgroup of `GL_r(ℝ)`, mapped to the orthogonal matrices. -/
def toUnitary (r : ℕ) : unitaryCompact ℝ r →* Matrix.unitaryGroup (Fin r) ℝ where
  toFun k := ⟨((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ), k.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toUnits_toUnitary (r : ℕ) (k : unitaryCompact ℝ r) :
    (Unitary.toUnits (toUnitary r k) : Langlands.GeneralLinear r ℝ) = k :=
  Units.ext rfl

theorem coe_toUnitary (r : ℕ) (k : unitaryCompact ℝ r) :
    ((toUnitary r k : Matrix.unitaryGroup (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ) =
      ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) :=
  rfl

/-- Right translation by `k ∈ O(r)` on the `O(r)`-finite functions of the real standard module
of `ds`. -/
def kRep (r : ℕ) (ds : List RealBlock) (k : unitaryCompact ℝ r) : KFin r ds →ₗ[ℂ] KFin r ds :=
  realStandardRep r ds (toUnitary r k)

theorem kRep_apply_coe (r : ℕ) (ds : List RealBlock) (k : unitaryCompact ℝ r) (f : KFin r ds)
    (g : Langlands.GeneralLinear r ℝ) :
    (kRep r ds k f : Langlands.GeneralLinear r ℝ → ℂ) g =
      (f : Langlands.GeneralLinear r ℝ → ℂ) (g * k) := by
  simp only [kRep, realStandardRep_apply_coe, toUnits_toUnitary]
  rfl

theorem kRep_mul (r : ℕ) (ds : List RealBlock) (k k' : unitaryCompact ℝ r) (f : KFin r ds) :
    kRep r ds (k * k') f = kRep r ds k (kRep r ds k' f) := by
  simp only [kRep, map_mul, Module.End.mul_apply]

theorem kRep_one (r : ℕ) (ds : List RealBlock) (f : KFin r ds) : kRep r ds 1 f = f := by
  simp only [kRep, map_one, Module.End.one_apply]

theorem kRep_inv_kRep (r : ℕ) (ds : List RealBlock) (k : unitaryCompact ℝ r) (f : KFin r ds) :
    kRep r ds k⁻¹ (kRep r ds k f) = f := by
  rw [← kRep_mul, inv_mul_cancel, kRep_one]

theorem kRep_kRep_inv (r : ℕ) (ds : List RealBlock) (k : unitaryCompact ℝ r) (f : KFin r ds) :
    kRep r ds k (kRep r ds k⁻¹ f) = f := by
  rw [← kRep_mul, mul_inv_cancel, kRep_one]

/-- The right derivative `R(X)` on the `O(r)`-finite functions of the real standard module of
`ds`. -/
def lie (r : ℕ) (ds : List RealBlock) (X : Matrix (Fin r) (Fin r) ℝ) :
    KFin r ds →ₗ[ℂ] KFin r ds :=
  realStandardLie r ds (1 ⊗ₜ X)

theorem lie_apply_coe (r : ℕ) (ds : List RealBlock) (X : Matrix (Fin r) (Fin r) ℝ)
    (f : KFin r ds) :
    (lie r ds X f : Langlands.GeneralLinear r ℝ → ℂ) =
      rightDerivative (matrixModel ℝ r) X (f : Langlands.GeneralLinear r ℝ → ℂ) :=
  realStandardLie_one_tmul_apply_coe r ds X f

/-- The adjoint action of `k ∈ O(r)` on real `r × r` matrices, `X ↦ k X k⁻¹`. -/
def adK (r : ℕ) (k : unitaryCompact ℝ r) (X : Matrix (Fin r) (Fin r) ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) * X *
    star ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ)

/-- `R(k) R(X) = R(k X k⁻¹) R(k)`. -/
theorem kRep_lie (r : ℕ) (ds : List RealBlock) (k : unitaryCompact ℝ r)
    (X : Matrix (Fin r) (Fin r) ℝ) (f : KFin r ds) :
    kRep r ds k (lie r ds X f) = lie r ds (adK r k X) (kRep r ds k f) :=
  (isRealGKModule_realStandardModule r ds).2.2.2 (toUnitary r k) X f

theorem coe_inv_unitaryCompact (r : ℕ) (k : unitaryCompact ℝ r) :
    (((k⁻¹ : unitaryCompact ℝ r) : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) =
      star ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) := by
  have h1 : ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) *
      (((k⁻¹ : unitaryCompact ℝ r) : Langlands.GeneralLinear r ℝ) :
        Matrix (Fin r) (Fin r) ℝ) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  have h2 : star ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) *
      ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp k.2
  calc (((k⁻¹ : unitaryCompact ℝ r) : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ)
      = (star ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) *
          ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ)) *
          (((k⁻¹ : unitaryCompact ℝ r) : Langlands.GeneralLinear r ℝ) :
            Matrix (Fin r) (Fin r) ℝ) := by rw [h2, one_mul]
    _ = star ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) := by
      rw [mul_assoc, h1, mul_one]

theorem adK_inv_adK (r : ℕ) (k : unitaryCompact ℝ r) (X : Matrix (Fin r) (Fin r) ℝ) :
    adK r k⁻¹ (adK r k X) = X := by
  have h2 : star ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) *
      ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp k.2
  simp only [adK, coe_inv_unitaryCompact, star_star]
  rw [show star ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) *
      (((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) * X *
        star ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ)) *
      ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) =
      (star ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) *
        ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ)) * X *
      (star ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) *
        ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ)) by
    simp only [mul_assoc], h2, one_mul, mul_one]

/-- `R(X) R(k⁻¹) = R(k⁻¹) R(k X k⁻¹)`. -/
theorem lie_kRep_inv (r : ℕ) (ds : List RealBlock) (k : unitaryCompact ℝ r)
    (X : Matrix (Fin r) (Fin r) ℝ) (f : KFin r ds) :
    lie r ds X (kRep r ds k⁻¹ f) = kRep r ds k⁻¹ (lie r ds (adK r k X) f) := by
  rw [kRep_lie, adK_inv_adK]

/-! ## Finite-dimensional `O(r)`-stable subspaces -/

variable {r : ℕ} {ds es : List RealBlock}

/-- Every finite-dimensional subspace of `O(r)`-finite functions lies in a finite-dimensional
`O(r)`-stable subspace. -/
theorem exists_stable (U : Submodule ℂ (KFin r ds)) [FiniteDimensional ℂ U] :
    ∃ S : Submodule ℂ (KFin r ds), FiniteDimensional ℂ S ∧ U ≤ S ∧
      ∀ k, ∀ v ∈ S, kRep r ds k v ∈ S := by
  have : Module.Free ℂ U := Module.Free.of_divisionRing ℂ U
  let b := Module.finBasis ℂ U
  let O := fun i => FiniteVectors.orbitSpan (realStandardRep r ds) (b i : KFin r ds)
  have hfin : ∀ i, FiniteDimensional ℂ (O i) := fun i =>
    (isRealGKModule_realStandardModule r ds).1 _
  refine ⟨⨆ i, O i, inferInstance, fun u hu => ?_, fun k v hv => ?_⟩
  · have hsum := b.sum_repr ⟨u, hu⟩
    have hval := congrArg (fun v : U => (v : KFin r ds)) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hval
    rw [← hval]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      ((le_iSup O i) (FiniteVectors.self_mem_orbitSpan _ _))
  · refine Submodule.iSup_induction O (motive := fun v => kRep r ds k v ∈ ⨆ i, O i) hv
      (fun i v hv => ?_) (by simp) (fun v w hv hw => by simpa using Submodule.add_mem _ hv hw)
    exact (le_iSup O i)
      ((FiniteVectors.orbitSubrepresentation (realStandardRep r ds) (b i : KFin r ds)
        ).apply_mem_toSubmodule (toUnitary r k) hv)

theorem kRep_mem_orbitSpan (k : unitaryCompact ℝ r) (f : KFin r ds) :
    kRep r ds k f ∈ FiniteVectors.orbitSpan (realStandardRep r ds) f :=
  FiniteVectors.action_mem_orbitSpan _ _ f

instance finiteDimensional_orbitSpan (f : KFin r ds) :
    FiniteDimensional ℂ (FiniteVectors.orbitSpan (realStandardRep r ds) f) :=
  (isRealGKModule_realStandardModule r ds).1 f

/-! ## The conjugates `R(k)⁻¹ A R(k)` -/

/-- The conjugate `R(k)⁻¹ ∘ A ∘ R(k)` of a linear map `A`. -/
def conj (A : KFin r ds →ₗ[ℂ] KFin r es) (k : unitaryCompact ℝ r) : KFin r ds →ₗ[ℂ] KFin r es :=
  kRep r es k⁻¹ ∘ₗ A ∘ₗ kRep r ds k

theorem conj_apply (A : KFin r ds →ₗ[ℂ] KFin r es) (k : unitaryCompact ℝ r) (f : KFin r ds) :
    conj A k f = kRep r es k⁻¹ (A (kRep r ds k f)) :=
  rfl

theorem conj_apply_coe (A : KFin r ds →ₗ[ℂ] KFin r es) (k : unitaryCompact ℝ r) (f : KFin r ds)
    (g : Langlands.GeneralLinear r ℝ) :
    (conj A k f : Langlands.GeneralLinear r ℝ → ℂ) g =
      (A (kRep r ds k f) : Langlands.GeneralLinear r ℝ → ℂ)
        (g * ((k⁻¹ : unitaryCompact ℝ r) : Langlands.GeneralLinear r ℝ)) := by
  rw [conj_apply, kRep_apply_coe]

/-- All conjugates `R(k)⁻¹ A (R(k) f)` lie in one finite-dimensional `O(r)`-stable subspace,
which also contains `A f`. -/
theorem exists_conj_stable (A : KFin r ds →ₗ[ℂ] KFin r es) (f : KFin r ds) :
    ∃ S : Submodule ℂ (KFin r es), FiniteDimensional ℂ S ∧ (∀ k, ∀ v ∈ S, kRep r es k v ∈ S) ∧
      A f ∈ S ∧ ∀ k, conj A k f ∈ S := by
  obtain ⟨S, hS, hUS, hstab⟩ :=
    exists_stable ((FiniteVectors.orbitSpan (realStandardRep r ds) f).map A)
  refine ⟨S, hS, hstab, hUS ⟨f, FiniteVectors.self_mem_orbitSpan _ f, rfl⟩, fun k => ?_⟩
  exact hstab _ _ (hUS ⟨_, kRep_mem_orbitSpan k f, rfl⟩)

theorem continuous_kRep_apply (f : KFin r ds) (g : Langlands.GeneralLinear r ℝ) :
    Continuous fun k : unitaryCompact ℝ r => (kRep r ds k f : Langlands.GeneralLinear r ℝ → ℂ) g := by
  simp_rw [kRep_apply_coe]
  exact (RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions f.2).comp
    (continuous_const.mul continuous_subtype_val)

/-- `k ↦ (R(k)⁻¹ A R(k) f)(g)` is continuous. -/
theorem continuous_conj_apply (A : KFin r ds →ₗ[ℂ] KFin r es) (f : KFin r ds)
    (g : Langlands.GeneralLinear r ℝ) :
    Continuous fun k : unitaryCompact ℝ r => (conj A k f : Langlands.GeneralLinear r ℝ → ℂ) g := by
  have heq : (fun k : unitaryCompact ℝ r => (conj A k f : Langlands.GeneralLinear r ℝ → ℂ) g) =
      fun k => (A (kRep r ds k f) : Langlands.GeneralLinear r ℝ → ℂ)
        (g * ((k⁻¹ : unitaryCompact ℝ r) : Langlands.GeneralLinear r ℝ)) :=
    funext fun k => conj_apply_coe A k f g
  rw [heq]
  let O := FiniteVectors.orbitSpan (realStandardRep r ds) f
  let U : Submodule ℂ (Langlands.GeneralLinear r ℝ → ℂ) := (O.map A).map (KFin r es).subtype
  have hjoint : Continuous fun p : unitaryCompact ℝ r × Langlands.GeneralLinear r ℝ =>
      (A (kRep r ds p.1 f) : Langlands.GeneralLinear r ℝ → ℂ) p.2 :=
    continuous_uncurry_of_mem U
      (fun u hu => by
        obtain ⟨v, -, rfl⟩ := hu
        exact RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions v.2)
      (fun k => ⟨_, ⟨_, kRep_mem_orbitSpan k f, rfl⟩, rfl⟩)
      (fun x => continuous_map_of_mem A O (fun k => kRep_mem_orbitSpan k f)
        (fun y => continuous_kRep_apply f y) x)
  have hinv : Continuous fun k : unitaryCompact ℝ r =>
      ((k⁻¹ : unitaryCompact ℝ r) : Langlands.GeneralLinear r ℝ) :=
    by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · have h : (Units.val ∘ fun k : unitaryCompact ℝ r =>
          ((k⁻¹ : unitaryCompact ℝ r) : Langlands.GeneralLinear r ℝ)) =
          fun k : unitaryCompact ℝ r =>
            star ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) :=
        funext fun k => coe_inv_unitaryCompact r k
      rw [h]
      exact continuous_star.comp (Units.continuous_val.comp continuous_subtype_val)
    · have h : (fun k : unitaryCompact ℝ r =>
          ((((k⁻¹ : unitaryCompact ℝ r) : Langlands.GeneralLinear r ℝ)⁻¹ :
            Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ)) =
          fun k : unitaryCompact ℝ r =>
            ((k : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) :=
        funext fun k => by rw [Subgroup.coe_inv, inv_inv]
      rw [h]
      exact Units.continuous_val.comp continuous_subtype_val
  have hφ : Continuous fun k : unitaryCompact ℝ r =>
      (k, g * ((k⁻¹ : unitaryCompact ℝ r) : Langlands.GeneralLinear r ℝ)) :=
    continuous_id.prodMk (continuous_const.mul hinv)
  have h3 := hjoint.comp hφ
  exact h3

theorem integrable_conj_apply (A : KFin r ds →ₗ[ℂ] KFin r es) (f : KFin r ds)
    (g : Langlands.GeneralLinear r ℝ) :
    Integrable (fun k : unitaryCompact ℝ r => (conj A k f : Langlands.GeneralLinear r ℝ → ℂ) g)
      (RealPrincipalSeriesDuality.haarK r) :=
  RealPrincipalSeriesDuality.integrable_of_continuous (continuous_conj_apply A f g)

theorem conj_kRep (A : KFin r ds →ₗ[ℂ] KFin r es) (k k0 : unitaryCompact ℝ r) (f : KFin r ds) :
    conj A k (kRep r ds k0 f) = kRep r es k0 (conj A (k * k0) f) := by
  simp only [conj_apply]
  rw [← kRep_mul r ds k k0, ← kRep_mul r es k0, mul_inv_rev, ← mul_assoc, mul_inv_cancel,
    one_mul]

/-! ## The average over `O(r)` -/

/-- The pointwise average of the conjugates `R(k)⁻¹ A (R(k) f)` is `O(r)`-finite. -/
theorem avg_mem (A : KFin r ds →ₗ[ℂ] KFin r es) (f : KFin r ds) :
    (fun g => ∫ k, (conj A k f : Langlands.GeneralLinear r ℝ → ℂ) g
      ∂RealPrincipalSeriesDuality.haarK r) ∈ KFin r es := by
  obtain ⟨S, hS, -, -, hconj⟩ := exists_conj_stable A f
  exact Submodule.map_subtype_le _ S
    (integral_mem _ (S.map (KFin r es).subtype) (fun k => coe_mem_map_subtype (hconj k))
      (integrable_conj_apply A f))

/-- The average `f ↦ ∫_{O(r)} R(k)⁻¹ A (R(k) f) dk` of a linear map `A` (normalized Haar
measure, pointwise integral). -/
def avg (A : KFin r ds →ₗ[ℂ] KFin r es) : KFin r ds →ₗ[ℂ] KFin r es where
  toFun f := ⟨_, avg_mem A f⟩
  map_add' f f' := by
    refine Subtype.ext (funext fun g => ?_)
    simp only [map_add, Submodule.coe_add, Pi.add_apply]
    exact integral_add (integrable_conj_apply A f g) (integrable_conj_apply A f' g)
  map_smul' c f := by
    refine Subtype.ext (funext fun g => ?_)
    simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

theorem avg_apply_coe (A : KFin r ds →ₗ[ℂ] KFin r es) (f : KFin r ds)
    (g : Langlands.GeneralLinear r ℝ) :
    (avg A f : Langlands.GeneralLinear r ℝ → ℂ) g =
      ∫ k, (conj A k f : Langlands.GeneralLinear r ℝ → ℂ) g ∂RealPrincipalSeriesDuality.haarK r :=
  rfl

/-- The average commutes exactly with right translation by `O(r)`. -/
theorem avg_kRep (A : KFin r ds →ₗ[ℂ] KFin r es) (k0 : unitaryCompact ℝ r) (f : KFin r ds) :
    avg A (kRep r ds k0 f) = kRep r es k0 (avg A f) := by
  refine Subtype.ext (funext fun g => ?_)
  rw [kRep_apply_coe, avg_apply_coe, avg_apply_coe]
  simp_rw [conj_kRep, kRep_apply_coe]
  exact integral_mul_right_eq_self
    (fun k => (conj A k f : Langlands.GeneralLinear r ℝ → ℂ) (g * k0)) k0

/-- If every conjugate `R(k)⁻¹ A (R(k) f)` differs from `c` by an element of `M`, so does the
average. -/
theorem avg_sub_mem (A : KFin r ds →ₗ[ℂ] KFin r es) (M : Submodule ℂ (KFin r es))
    (f : KFin r ds) (c : KFin r es) (h : ∀ k, conj A k f - c ∈ M) : avg A f - c ∈ M := by
  obtain ⟨S, hS, -, -, hconj⟩ := exists_conj_stable A f
  refine mem_of_integral (RealPrincipalSeriesDuality.haarK r) M (S ⊔ Submodule.span ℂ {c})
    (w := fun k => conj A k f - c) (fun k => ⟨?_, h k⟩) (fun g => ?_) (fun g => ?_)
  · exact Submodule.sub_mem _ (Submodule.mem_sup_left (hconj k))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self c))
  · simp only [Submodule.coe_sub, Pi.sub_apply]
    exact (integrable_conj_apply A f g).sub (integrable_const _)
  · simp only [Submodule.coe_sub, Pi.sub_apply]
    rw [integral_sub (integrable_conj_apply A f g) (integrable_const _), integral_const,
      avg_apply_coe]
    simp

/-- If every conjugate `R(k)⁻¹ A (R(k) f)` lies in `M`, so does the average. -/
theorem avg_mem_of_forall (A : KFin r ds →ₗ[ℂ] KFin r es) (M : Submodule ℂ (KFin r es))
    (f : KFin r ds) (h : ∀ k, conj A k f ∈ M) : avg A f ∈ M := by
  simpa using avg_sub_mem A M f 0 (by simpa using h)

/-- If `M` is `O(r)`-stable and `A` commutes with `O(r)` modulo `M`, then `avg A f - A f ∈ M`. -/
theorem avg_sub_self_mem (A : KFin r ds →ₗ[ℂ] KFin r es) (M : Submodule ℂ (KFin r es))
    (hM : ∀ k, ∀ v ∈ M, kRep r es k v ∈ M)
    (hA : ∀ k f, A (kRep r ds k f) - kRep r es k (A f) ∈ M) (f : KFin r ds) :
    avg A f - A f ∈ M := by
  refine avg_sub_mem A M f (A f) fun k => ?_
  have h := hM k⁻¹ _ (hA k f)
  rwa [map_sub, kRep_inv_kRep] at h

/-- An exactly `O(r)`-equivariant `A` is its own average. -/
theorem avg_eq_self (A : KFin r ds →ₗ[ℂ] KFin r es)
    (hA : ∀ k f, A (kRep r ds k f) = kRep r es k (A f)) (f : KFin r ds) : avg A f = A f := by
  have h := avg_sub_self_mem A ⊥ (fun _ _ hv => by
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]) (fun k f => by rw [hA, sub_self]; exact Submodule.zero_mem _) f
  rwa [Submodule.mem_bot, sub_eq_zero] at h

variable {fs : List RealBlock}

/-- An exactly `O(r)`-equivariant `B` satisfies `B ∘ avg A = avg (B ∘ A)`. -/
theorem map_avg (A : KFin r ds →ₗ[ℂ] KFin r es) (B : KFin r es →ₗ[ℂ] KFin r fs)
    (hB : ∀ k v, B (kRep r es k v) = kRep r fs k (B v)) (f : KFin r ds) :
    B (avg A f) = avg (B ∘ₗ A) f := by
  obtain ⟨S, hS, -, -, hconj⟩ := exists_conj_stable A f
  refine Subtype.ext (funext fun g => ?_)
  rw [map_integral_of_mem (RealPrincipalSeriesDuality.haarK r) B S hconj
    (integrable_conj_apply A f) (fun x => avg_apply_coe A f x) g, avg_apply_coe]
  congr 1
  funext k
  simp only [conj_apply, LinearMap.comp_apply, hB]

/-- If `M` is `O(r)`-stable and `A` commutes with all right derivatives modulo `M`, so does its
average. -/
theorem lie_avg_sub_mem (A : KFin r ds →ₗ[ℂ] KFin r es) (M : Submodule ℂ (KFin r es))
    (hM : ∀ k, ∀ v ∈ M, kRep r es k v ∈ M)
    (hA : ∀ (Y : Matrix (Fin r) (Fin r) ℝ) f, lie r es Y (A f) - A (lie r ds Y f) ∈ M)
    (X : Matrix (Fin r) (Fin r) ℝ) (f : KFin r ds) :
    lie r es X (avg A f) - avg A (lie r ds X f) ∈ M := by
  obtain ⟨S, hS, -, -, hconj⟩ := exists_conj_stable A f
  obtain ⟨S', hS', -, -, hconj'⟩ := exists_conj_stable A (lie r ds X f)
  have hlie : ∀ g, Integrable (fun k => (lie r es X (conj A k f) :
      Langlands.GeneralLinear r ℝ → ℂ) g) (RealPrincipalSeriesDuality.haarK r) := fun g =>
    RealPrincipalSeriesDuality.integrable_of_continuous
      (continuous_map_of_mem (lie r es X) S hconj (continuous_conj_apply A f) g)
  refine mem_of_integral (RealPrincipalSeriesDuality.haarK r) M (S.map (lie r es X) ⊔ S')
    (w := fun k => lie r es X (conj A k f) - conj A k (lie r ds X f)) (fun k => ⟨?_, ?_⟩)
    (fun g => ?_) (fun g => ?_)
  · exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨_, hconj k, rfl⟩)
      (Submodule.mem_sup_right (hconj' k))
  · have h := hM k⁻¹ _ (hA (adK r k X) (kRep r ds k f))
    simp only [conj_apply]
    rw [lie_kRep_inv, kRep_lie r ds k X f, ← map_sub]
    exact h
  · simp only [Submodule.coe_sub, Pi.sub_apply]
    exact (hlie g).sub (integrable_conj_apply A _ g)
  · simp only [Submodule.coe_sub, Pi.sub_apply]
    rw [integral_sub (hlie g) (integrable_conj_apply A _ g),
      map_integral_of_mem (RealPrincipalSeriesDuality.haarK r) (lie r es X) S hconj
        (integrable_conj_apply A f) (fun x => avg_apply_coe A f x) g, avg_apply_coe]

end InductionStages

end Langlands.Archimedean
