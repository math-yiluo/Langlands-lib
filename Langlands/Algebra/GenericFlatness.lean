import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Generic flatness over a noetherian domain -/

open TensorProduct

universe u v w

namespace Langlands.Algebra.GenericFlatness

section General

variable {A : Type u} [CommRing A]
variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

/-- The multiplication maps `I ⊗ M → M` are natural in `M`. -/
theorem lift_lsmul_lTensor (I : Ideal A) (f : M₁ →ₗ[A] M₂) (x : I ⊗[A] M₁) :
    TensorProduct.lift ((LinearMap.lsmul A M₂).comp I.subtype) (f.lTensor I x) =
      f (TensorProduct.lift ((LinearMap.lsmul A M₁).comp I.subtype) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r m => simp
  | add x y hx hy => simp [hx, hy]

/-- An extension of flat modules is flat. -/
theorem flat_of_exact (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) [Module.Flat A M₁]
    [Module.Flat A M₃] : Module.Flat A M₂ := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I hI
  have h₁ := Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp ‹Module.Flat A M₁› hI
  have h₃ := Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp ‹Module.Flat A M₃› hI
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hex : Function.Exact (f.lTensor I) (g.lTensor I) := lTensor_exact I hfg hg
  have hgx : g.lTensor I x = 0 := by
    apply h₃
    rw [lift_lsmul_lTensor, hx, map_zero, map_zero]
  obtain ⟨y, rfl⟩ := (hex x).mp hgx
  rw [lift_lsmul_lTensor] at hx
  have hy : TensorProduct.lift ((LinearMap.lsmul A M₁).comp I.subtype) y = 0 :=
    hf (hx.trans f.map_zero.symm)
  rw [h₁ (hy.trans (map_zero _).symm), map_zero]

/-- A module covered by a directed family of flat submodules is flat. -/
theorem flat_of_directed {ι : Type*} [Nonempty ι] (N : ι → Submodule A M₂)
    (hN : Directed (· ≤ ·) N) (hcov : ∀ m, ∃ i, m ∈ N i) (hflat : ∀ i, Module.Flat A (N i)) :
    Module.Flat A M₂ := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I hI
  have hrange : ∀ x : I ⊗[A] M₂, ∃ i, ∃ y : I ⊗[A] N i, (N i).subtype.lTensor I y = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r m =>
      obtain ⟨i, hi⟩ := hcov m
      exact ⟨i, r ⊗ₜ ⟨m, hi⟩, by simp⟩
    | add x y hx hy =>
      obtain ⟨i, x', rfl⟩ := hx
      obtain ⟨j, y', rfl⟩ := hy
      obtain ⟨k, hik, hjk⟩ := hN i j
      refine ⟨k, (Submodule.inclusion hik).lTensor I x' + (Submodule.inclusion hjk).lTensor I y',
        ?_⟩
      rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
        ← LinearMap.lTensor_comp]
      rfl
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, y, rfl⟩ := hrange x
  have hi := Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp (hflat i) hI
  rw [lift_lsmul_lTensor] at hx
  have hy : TensorProduct.lift ((LinearMap.lsmul A (N i)).comp I.subtype) y = 0 :=
    Subtype.ext hx
  rw [hi (hy.trans (map_zero _).symm), map_zero]

/-- A localization of a flat module is flat over the base. -/
theorem flat_localizedModule (S : Submonoid A) [Module.Flat A M₁] :
    Module.Flat A (LocalizedModule S M₁) :=
  Module.Flat.trans A (Localization S) (LocalizedModule S M₁)

/-- Flatness of a localization only depends on the localization up to isomorphism. -/
theorem flat_localizedModule_iff (S : Submonoid A) (f : M₁ →ₗ[A] M₂) [IsLocalizedModule S f] :
    Module.Flat A (LocalizedModule S M₁) ↔ Module.Flat A M₂ :=
  Module.Flat.equiv_iff (IsLocalizedModule.iso S f)

/-- Localizing further preserves flatness of a localization. -/
theorem flat_localizedModule_of_le {S T : Submonoid A} (h : S ≤ T)
    [Module.Flat A (LocalizedModule S M₁)] : Module.Flat A (LocalizedModule T M₁) := by
  have : Module.Flat (Localization T) (LocalizedModule T M₁) :=
    Module.Flat.of_isLocalizedModule (Localization T) T
      (LocalizedModule.liftOfLE S T h (M := M₁))
  exact Module.Flat.trans A (Localization T) (LocalizedModule T M₁)

/-- Flatness after localization transfers along linear equivalences. -/
theorem flat_localizedModule_of_equiv (S : Submonoid A) (e : M₁ ≃ₗ[A] M₂)
    [Module.Flat A (LocalizedModule S M₁)] : Module.Flat A (LocalizedModule S M₂) := by
  have : IsLocalizedModule S ((LocalizedModule.mkLinearMap S M₁).comp e.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S _ _
  exact (flat_localizedModule_iff S ((LocalizedModule.mkLinearMap S M₁).comp
    e.symm.toLinearMap)).mpr ‹_›

/-- An extension of modules whose localizations are flat has flat localization. -/
theorem flat_localizedModule_of_exact (S : Submonoid A) (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.Flat A (LocalizedModule S M₁)] [Module.Flat A (LocalizedModule S M₃)] :
    Module.Flat A (LocalizedModule S M₂) :=
  flat_of_exact
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M₁)
      (LocalizedModule.mkLinearMap S M₂) f)
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M₂)
      (LocalizedModule.mkLinearMap S M₃) g)
    (IsLocalizedModule.map_injective _ _ _ _ hf) (IsLocalizedModule.map_surjective _ _ _ _ hg)
    (LocalizedModule.map_exact S f g hfg)

variable (A) in
/-- `M` is generically flat over `A`: for some nonzero `a : A`, every localization `M_b` at a
multiple `b` of `a` is flat over `A`. -/
def GenFlat (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∃ a : A, a ≠ 0 ∧ ∀ b : A, a ∣ b → Module.Flat A (LocalizedModule (Submonoid.powers b) M)

/-- Flatness of `M_a` gives flatness of `M_b` whenever `a ∣ b`. -/
theorem flat_localizedModule_powers_of_dvd {a b : A} (h : a ∣ b)
    [Module.Flat A (LocalizedModule (Submonoid.powers a) M₁)] :
    Module.Flat A (LocalizedModule (Submonoid.powers b) M₁) := by
  let T : Submonoid A :=
    { carrier := {x | ∃ n : ℕ, x ∣ b ^ n}
      mul_mem' := fun {x y} ⟨n, hn⟩ ⟨m, hm⟩ => ⟨n + m, pow_add b n m ▸ mul_dvd_mul hn hm⟩
      one_mem' := ⟨0, one_dvd _⟩ }
  have hle : Submonoid.powers a ≤ T := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, pow_dvd_pow_of_dvd h n⟩
  have hbT : Submonoid.powers b ≤ T := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, dvd_rfl⟩
  have hT : Module.Flat A (LocalizedModule T M₁) := flat_localizedModule_of_le hle
  have : IsLocalizedModule T (LocalizedModule.mkLinearMap (Submonoid.powers b) M₁) :=
    IsLocalizedModule.of_exists_mul_mem (Submonoid.powers b) T hbT (by
      rintro ⟨x, n, c, hc⟩
      exact ⟨c, n, by change b ^ n = c * x; rw [hc, mul_comm]⟩) _
  exact (flat_localizedModule_iff T (LocalizedModule.mkLinearMap (Submonoid.powers b) M₁)).mp hT

theorem GenFlat.of_equiv (e : M₁ ≃ₗ[A] M₂) (h : GenFlat A M₁) : GenFlat A M₂ := by
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a, ha, fun b hb => ?_⟩
  have := h b hb
  exact flat_localizedModule_of_equiv _ e

theorem GenFlat.of_exact [IsDomain A] (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h₁ : GenFlat A M₁) (h₃ : GenFlat A M₃) : GenFlat A M₂ := by
  obtain ⟨a₁, ha₁, h₁⟩ := h₁
  obtain ⟨a₃, ha₃, h₃⟩ := h₃
  refine ⟨a₁ * a₃, mul_ne_zero ha₁ ha₃, fun b hb => ?_⟩
  have := h₁ b (dvd_trans (dvd_mul_right a₁ a₃) hb)
  have := h₃ b (dvd_trans (dvd_mul_left a₃ a₁) hb)
  exact flat_localizedModule_of_exact _ f g hf hg hfg

/-- Generic freeness, hence generic flatness, of a finite module over a noetherian domain. -/
theorem GenFlat.of_finite [IsDomain A] [IsNoetherianRing A] (M : Type*) [AddCommGroup M]
    [Module A M] [Module.Finite A M] : GenFlat A M := by
  have := Module.finitePresentation_of_finite A M
  have : Module.Free (FractionRing A) (LocalizedModule (nonZeroDivisors A) M) :=
    Module.Free.of_divisionRing _ _
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  refine ⟨r, nonZeroDivisors.ne_zero hr, fun b hb => ?_⟩
  have : Module.Flat A (LocalizedModule (Submonoid.powers r) M) :=
    Module.Flat.trans A (Localization (Submonoid.powers r)) _
  exact flat_localizedModule_powers_of_dvd hb

end General

section Filtration

variable {R : Type v} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]
variable (τ : M →ₗ[R] M) (N : Submodule R M)

/-- The filtration `N + τ N + ⋯ + τ^k N`. -/
def filt : ℕ → Submodule R M
  | 0 => N
  | k + 1 => filt k ⊔ N.map (τ ^ (k + 1))

theorem filt_zero : filt τ N 0 = N := rfl

theorem filt_succ (k : ℕ) : filt τ N (k + 1) = filt τ N k ⊔ N.map (τ ^ (k + 1)) := rfl

theorem filt_mono : Monotone (filt τ N) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

theorem map_filt_le (k : ℕ) : (filt τ N k).map τ ≤ filt τ N (k + 1) := by
  induction k with
  | zero => exact le_sup_of_le_right (by rw [pow_one]; rfl)
  | succ k ih =>
    rw [filt_succ τ N k, Submodule.map_sup]
    refine sup_le (ih.trans le_sup_left) ?_
    rw [← Submodule.map_comp]
    have : τ.comp (τ ^ (k + 1)) = τ ^ (k + 1 + 1) := by rw [pow_succ' τ (k + 1)]; rfl
    rw [this]
    exact le_sup_right

theorem apply_mem_filt {k : ℕ} {m : M} (hm : m ∈ filt τ N k) : τ m ∈ filt τ N (k + 1) :=
  map_filt_le τ N k (Submodule.mem_map_of_mem hm)

/-- The elements of `N` whose `(k+1)`-st iterate lies in `filt k`. -/
def L (k : ℕ) : Submodule R N := (filt τ N k).comap ((τ ^ (k + 1)).comp N.subtype)

theorem L_mono : Monotone (L τ N) := by
  refine monotone_nat_of_le_succ fun k x hx => ?_
  change (τ ^ (k + 1 + 1)) x ∈ filt τ N (k + 1)
  rw [pow_succ', Module.End.mul_apply]
  exact apply_mem_filt τ N hx

/-- The map `N → filt (k+1) / filt k`, `x ↦ [τ^(k+1) x]`. -/
noncomputable def succMap (k : ℕ) :
    N →ₗ[R] filt τ N (k + 1) ⧸ (filt τ N k).comap (filt τ N (k + 1)).subtype :=
  ((filt τ N k).comap (filt τ N (k + 1)).subtype).mkQ ∘ₗ
    ((τ ^ (k + 1)).comp N.subtype).codRestrict (filt τ N (k + 1)) fun x =>
      Submodule.mem_sup_right (Submodule.mem_map_of_mem x.2)

theorem succMap_surjective (k : ℕ) : Function.Surjective (succMap τ N k) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp z.2
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
  refine ⟨⟨x, hx⟩, (Submodule.Quotient.eq _).mpr ?_⟩
  change (τ ^ (k + 1)) x - z ∈ filt τ N k
  rw [← huv, sub_add_cancel_right]
  exact neg_mem hu

theorem ker_succMap (k : ℕ) : LinearMap.ker (succMap τ N k) = L τ N k := by
  ext x
  simp only [LinearMap.mem_ker, succMap, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

/-- The successive quotients of the filtration are quotients of `N`. -/
noncomputable def quotEquiv (k : ℕ) :
    (N ⧸ L τ N k) ≃ₗ[R] filt τ N (k + 1) ⧸ (filt τ N k).comap (filt τ N (k + 1)).subtype :=
  (Submodule.quotEquivOfEq _ _ (ker_succMap τ N k).symm).trans
    ((succMap τ N k).quotKerEquivOfSurjective (succMap_surjective τ N k))

theorem exact_inclusion_mkQ {p q : Submodule R M} (h : p ≤ q) :
    Function.Exact (Submodule.inclusion h) (p.comap q.subtype).mkQ := by
  intro y
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Set.mem_range]
  constructor
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.2

section Scalars

variable {A : Type u} [CommRing A] [Algebra A R] [Module A M] [IsScalarTower A R M]

theorem flat_localizedModule_of_le_quot (S : Submonoid A) {p q : Submodule R M} (h : p ≤ q)
    [Module.Flat A (LocalizedModule S p)]
    [Module.Flat A (LocalizedModule S (q ⧸ p.comap q.subtype))] :
    Module.Flat A (LocalizedModule S q) :=
  flat_localizedModule_of_exact S ((Submodule.inclusion h).restrictScalars A)
    ((p.comap q.subtype).mkQ.restrictScalars A) (Submodule.inclusion_injective h)
    (Submodule.mkQ_surjective (p.comap q.subtype)) (exact_inclusion_mkQ h)

theorem genFlat_of_le_quot [IsDomain A] {p q : Submodule R M} (h : p ≤ q) (hp : GenFlat A p)
    (hq : GenFlat A (q ⧸ p.comap q.subtype)) : GenFlat A q :=
  GenFlat.of_exact ((Submodule.inclusion h).restrictScalars A)
    ((p.comap q.subtype).mkQ.restrictScalars A) (Submodule.inclusion_injective h)
    (Submodule.mkQ_surjective (p.comap q.subtype)) (exact_inclusion_mkQ h) hp hq

end Scalars

end Filtration

section Induction

variable {A : Type u} [CommRing A] {R : Type v} [CommRing R] [Algebra A R]

variable (A R) in
/-- Every finite `R`-module (in universe `w`) is generically flat over `A`. -/
def GF : Prop :=
  ∀ (M : Type w) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]
    [Module.Finite R M], GenFlat A M

/-- The inductive step: a module filtered by the iterates of a finite submodule under an
endomorphism is generically flat. -/
theorem genFlat_of_filt [IsDomain A] [IsNoetherianRing R] (hR : GF.{u, v, w} A R)
    {M : Type w} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]
    (τ : M →ₗ[R] M) (N : Submodule R M) [Module.Finite R N]
    (hcov : ∀ m : M, ∃ k, m ∈ filt τ N k) : GenFlat A M := by
  have hL : ∀ k, GenFlat A (N ⧸ L τ N k) := fun k => hR _
  have hS : ∀ k, GenFlat A (filt τ N (k + 1) ⧸ (filt τ N k).comap (filt τ N (k + 1)).subtype) :=
    fun k => (hL k).of_equiv ((quotEquiv τ N k).restrictScalars A)
  have h1 : ∀ k, GenFlat A (filt τ N k) := by
    intro k
    induction k with
    | zero => exact hR N
    | succ k ih =>
      exact genFlat_of_le_quot (filt_mono τ N k.le_succ) ih (hS k)
  obtain ⟨k₀, hk₀⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance ⟨L τ N, L_mono τ N⟩
  obtain ⟨a₀, ha₀, h₀⟩ := h1 k₀
  obtain ⟨a₁, ha₁, h₁⟩ := hL k₀
  refine ⟨a₀ * a₁, mul_ne_zero ha₀ ha₁, fun b hb => ?_⟩
  let S := Submonoid.powers b
  have hfl : ∀ j, Module.Flat A (LocalizedModule S (filt τ N (k₀ + j))) := by
    intro j
    induction j with
    | zero => exact h₀ b (dvd_trans (dvd_mul_right _ _) hb)
    | succ j ih =>
      have : Module.Flat A (LocalizedModule S (N ⧸ L τ N (k₀ + j))) := by
        have := h₁ b (dvd_trans (dvd_mul_left _ _) hb)
        exact flat_localizedModule_of_equiv _
          ((Submodule.quotEquivOfEq _ _ (hk₀ (k₀ + j) (by omega))).restrictScalars A)
      have : Module.Flat A (LocalizedModule S
          (filt τ N (k₀ + j + 1) ⧸ (filt τ N (k₀ + j)).comap (filt τ N (k₀ + j + 1)).subtype)) :=
        flat_localizedModule_of_equiv _ ((quotEquiv τ N (k₀ + j)).restrictScalars A)
      exact flat_localizedModule_of_le_quot S (filt_mono τ N (k₀ + j).le_succ)
  let f := LocalizedModule.mkLinearMap S M
  let Q : ℕ → Submodule A (LocalizedModule S M) := fun j =>
    ((filt τ N (k₀ + j)).restrictScalars A).localized₀ S f
  refine flat_of_directed Q (Monotone.directed_le fun i j hij => ?_) (fun x => ?_) (fun j => ?_)
  · rintro _ ⟨m, hm, s, rfl⟩
    exact ⟨m, filt_mono τ N (by omega) hm, s, rfl⟩
  · obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
    obtain ⟨k, hk⟩ := hcov m
    exact ⟨k, m, filt_mono τ N (by omega) hk, s, rfl⟩
  · have : Module.Flat A (LocalizedModule S ((filt τ N (k₀ + j)).restrictScalars A)) :=
      flat_localizedModule_of_equiv _
        ((Submodule.restrictScalarsEquiv A R M (filt τ N (k₀ + j))).symm.restrictScalars A)
    exact (flat_localizedModule_iff S
      (((filt τ N (k₀ + j)).restrictScalars A).toLocalized₀ S f)).mp this

/-- Passing from `R` to `R[X]`. -/
theorem gf_polynomial [IsDomain A] [IsNoetherianRing R] (hR : GF.{u, v, w} A R) :
    GF.{u, v, w} A (Polynomial R) := by
  intro M _ _ _ _ _
  let _ : Module R M := Module.compHom M (Polynomial.C : R →+* Polynomial R)
  have : IsScalarTower R (Polynomial R) M :=
    ⟨fun r p m => by
      change (r • p) • m = Polynomial.C r • (p • m)
      rw [Polynomial.smul_eq_C_mul, mul_smul]⟩
  have : IsScalarTower A R M :=
    ⟨fun a r m => by
      change Polynomial.C (a • r) • m = a • (Polynomial.C r • m)
      rw [← smul_assoc, Polynomial.smul_C]⟩
  let τ : M →ₗ[R] M :=
    { toFun := fun m => (Polynomial.X : Polynomial R) • m
      map_add' := smul_add _
      map_smul' := fun r m => by
        change (Polynomial.X : Polynomial R) • Polynomial.C r • m =
          Polynomial.C r • (Polynomial.X : Polynomial R) • m
        rw [smul_smul, smul_smul, mul_comm] }
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := Polynomial R) (M := M)
  let N := Submodule.span R (G : Set M)
  refine genFlat_of_filt hR τ N fun m => ?_
  let W : Submodule (Polynomial R) M :=
    { carrier := {m | ∃ k, m ∈ filt τ N k}
      add_mem' := fun {x y} ⟨k, hk⟩ ⟨l, hl⟩ => ⟨max k l,
        add_mem (filt_mono τ N (le_max_left k l) hk) (filt_mono τ N (le_max_right k l) hl)⟩
      zero_mem' := ⟨0, zero_mem _⟩
      smul_mem' := fun p x ⟨k, hk⟩ => by
        induction p using Polynomial.induction_on with
        | C r => exact ⟨k, (filt τ N k).smul_mem r hk⟩
        | add p q hp hq =>
          obtain ⟨k₁, hk₁⟩ := hp
          obtain ⟨k₂, hk₂⟩ := hq
          refine ⟨max k₁ k₂, ?_⟩
          rw [add_smul]
          exact add_mem (filt_mono τ N (le_max_left _ _) hk₁)
            (filt_mono τ N (le_max_right _ _) hk₂)
        | monomial n r ih =>
          obtain ⟨k', hk'⟩ := ih
          refine ⟨k' + 1, ?_⟩
          have : Polynomial.C r * Polynomial.X ^ (n + 1) =
              Polynomial.X * (Polynomial.C r * Polynomial.X ^ n) := by ring
          rw [this, mul_smul]
          exact apply_mem_filt τ N hk' }
  have hW : W = ⊤ := by
    rw [eq_top_iff, ← hG, Submodule.span_le]
    intro g hg
    exact ⟨0, Submodule.subset_span hg⟩
  have : m ∈ W := hW ▸ Submodule.mem_top
  exact this

/-- Generic flatness descends along surjections of algebras. -/
theorem gf_of_surjective {D : Type*} [CommRing D] [Algebra A D] (φ : R →ₐ[A] D)
    (hφ : Function.Surjective φ) (h : GF.{u, v, w} A R) : GF.{u, _, w} A D := by
  intro M _ _ _ _ _
  let _ : Module R M := Module.compHom M φ.toRingHom
  have : IsScalarTower A R M :=
    ⟨fun a r m => by
      change φ (a • r) • m = a • (φ r • m)
      rw [map_smul, smul_assoc]⟩
  have : Module.Finite R M := by
    obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := D) (M := M)
    let W : Submodule D M :=
      { (Submodule.span R (G : Set M)).toAddSubmonoid with
        smul_mem' := fun d m hm => by
          obtain ⟨r, rfl⟩ := hφ d
          exact (Submodule.span R (G : Set M)).smul_mem r hm }
    have hW : W = ⊤ := by
      rw [eq_top_iff, ← hG, Submodule.span_le]
      exact Submodule.subset_span
    refine ⟨⟨G, eq_top_iff.mpr fun m _ => ?_⟩⟩
    have : m ∈ W := hW ▸ Submodule.mem_top
    exact this
  exact h M

theorem gf_of_finite [IsDomain A] [IsNoetherianRing A] [Module.Finite A R] :
    GF.{u, v, w} A R := by
  intro M _ _ _ _ _
  have : Module.Finite A M := Module.Finite.trans R M
  exact GenFlat.of_finite M

theorem gf_mvPolynomial [IsDomain A] [IsNoetherianRing A] (n : ℕ) :
    GF.{u, u, w} A (MvPolynomial (Fin n) A) := by
  induction n with
  | zero =>
    have : Module.Finite A (MvPolynomial (Fin 0) A) :=
      Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).toLinearEquiv.symm
    exact gf_of_finite
  | succ n ih =>
    exact gf_of_surjective (MvPolynomial.finSuccEquiv A n).symm.toAlgHom
      (MvPolynomial.finSuccEquiv A n).symm.surjective (gf_polynomial ih)

end Induction

/-- **Generic flatness.** A finite module over a finite type algebra over a noetherian domain
`A` becomes flat over `A` after inverting a suitable nonzero element of `A`, and remains so
after inverting any multiple of it. -/
theorem genFlat_of_finiteType {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (B : Type v) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type w) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] : GenFlat A M := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  exact gf_of_surjective f hf (gf_mvPolynomial.{u, w} n) M

end Langlands.Algebra.GenericFlatness
