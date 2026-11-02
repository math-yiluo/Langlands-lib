import Langlands.Algebra.NonUnitalSimplicityStatements
import Mathlib.Tactic.LinearCombination

/-!
# Proof of the actual-action simplicity and scalar-linearity reductions

This proves `NonUnitalSimplicityReductionStatement.{uK, uA, uM, uN}` from
`Langlands.Algebra.NonUnitalSimplicityStatements`, for the actual original action
`NonUnitalModule.ofLinearEndHom ρ` and the actual unitized action `CompatibleUnitization.module ρ`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra

universe uK uA uM uN

/-! ### Categorical simplicity of an original module -/

namespace NonUnitalModuleCat

variable {A : Type uA} [NonUnitalRing A]

/-- The zero stable additive subgroup. -/
def botSubmodule (X : NonUnitalModuleCat.{uA, uM} A) : NonUnitalSubmodule A X where
  toAddSubgroup := ⊥
  smul_mem' a m hm := by
    rw [AddSubgroup.mem_bot] at hm ⊢
    rw [hm, smul_zero]

/-- The whole stable additive subgroup. -/
def topSubmodule (X : NonUnitalModuleCat.{uA, uM} A) : NonUnitalSubmodule A X where
  toAddSubgroup := ⊤
  smul_mem' _ _ _ := AddSubgroup.mem_top _

/-- A stable additive subgroup is determined by its underlying additive subgroup. -/
theorem toAddSubgroup_injective (X : NonUnitalModuleCat.{uA, uM} A) :
    Function.Injective
      (NonUnitalSubmodule.toAddSubgroup : NonUnitalSubmodule A X → AddSubgroup X) :=
  fun _ _ h => SetLike.coe_injective (congrArg (fun H : AddSubgroup X => (H : Set X)) h)

/-- The top subobject corresponds to the whole module. -/
theorem subobjectOrderIso_top (X : NonUnitalModuleCat.{uA, uM} A) :
    subobjectOrderIso X ⊤ = topSubmodule X := by
  rw [Subobject.top_eq_id]
  exact SetLike.ext fun m => (mem_subobjectOrderIso_mk (𝟙 X) m).trans
    ⟨fun _ => AddSubgroup.mem_top m, fun _ => ⟨m, rfl⟩⟩

/-- The bottom subobject corresponds to the zero stable additive subgroup. -/
theorem subobjectOrderIso_bot (X : NonUnitalModuleCat.{uA, uM} A)
    [HasZeroObject (NonUnitalModuleCat.{uA, uM} A)] :
    subobjectOrderIso X ⊥ = botSubmodule X :=
  le_antisymm ((subobjectOrderIso X).le_symm_apply.1 bot_le) fun m hm => by
    have hm0 : m = 0 := AddSubgroup.mem_bot.1 hm
    rw [hm0]
    exact (subobjectOrderIso X ⊥).toAddSubgroup.zero_mem

/-- Additive simplicity of an original module is categorical simplicity. -/
theorem additiveSimple_iff_simple (X : NonUnitalModuleCat.{uA, uM} A) :
    (Nontrivial X ∧ ∀ S : NonUnitalSubmodule A X, S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) ↔
      Simple X := by
  have : HasFiniteBiproducts (NonUnitalModuleCat.{uA, uM} A) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasZeroObject (NonUnitalModuleCat.{uA, uM} A) := hasZeroObject_of_hasFiniteBiproducts _
  rw [simple_iff_subobject_isSimpleOrder]
  have hbot : ∀ S : NonUnitalSubmodule A X, S = botSubmodule X ↔ S.toAddSubgroup = ⊥ :=
    fun S => (toAddSubgroup_injective X).eq_iff.symm
  have htop : ∀ S : NonUnitalSubmodule A X, S = topSubmodule X ↔ S.toAddSubgroup = ⊤ :=
    fun S => (toAddSubgroup_injective X).eq_iff.symm
  constructor
  · rintro ⟨hnt, hS⟩
    have : Nontrivial (Subobject X) := nontrivial_of_ne ⊥ ⊤ fun h => by
      have h' := congrArg (fun P => (subobjectOrderIso X P).toAddSubgroup) h
      simp only [subobjectOrderIso_bot, subobjectOrderIso_top] at h'
      exact bot_ne_top h'
    refine ⟨fun P => ?_⟩
    rcases hS (subobjectOrderIso X P) with h | h
    · left
      apply (subobjectOrderIso X).injective
      rw [subobjectOrderIso_bot]
      exact (hbot _).2 h
    · right
      apply (subobjectOrderIso X).injective
      rw [subobjectOrderIso_top]
      exact (htop _).2 h
  · intro hs
    refine ⟨?_, fun S => ?_⟩
    · by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      apply (bot_ne_top : (⊥ : Subobject X) ≠ ⊤)
      apply (subobjectOrderIso X).injective
      rw [subobjectOrderIso_bot, subobjectOrderIso_top]
      refine SetLike.ext fun m => ?_
      change m ∈ (⊥ : AddSubgroup X) ↔ m ∈ (⊤ : AddSubgroup X)
      exact ⟨fun _ => AddSubgroup.mem_top m,
        fun _ => AddSubgroup.mem_bot.2 (Subsingleton.elim m 0)⟩
    · rcases eq_bot_or_eq_top ((subobjectOrderIso X).symm S) with h | h
      · left
        rw [← hbot, ← subobjectOrderIso_bot, ← h, OrderIso.apply_symm_apply]
      · right
        rw [← htop, ← subobjectOrderIso_top, ← h, OrderIso.apply_symm_apply]

end NonUnitalModuleCat

namespace CompatibleUnitization

open Unitization

/-! ### The categorical comparison -/

section Categorical

variable {k : Type uK} [Field k] {A : Type uA} [NonUnitalRing A] [Module k A]
  {M : Type uM} [AddCommGroup M] [Module k M]

/-- Comparison 2: original additive simplicity is categorical simplicity. -/
theorem additiveSimpleCategorical (ρ : A →ₙₐ[k] Module.End k M) :
    AdditiveSimpleCategoricalStatement ρ :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  NonUnitalModuleCat.additiveSimple_iff_simple (NonUnitalModuleCat.of A M)

end Categorical

section General

variable {k : Type uK} [Field k] {A : Type uA} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  {M : Type uM} [AddCommGroup M] [Module k M]

/-- Comparison 1: simplicity of stable vector subspaces is simplicity of the unitized module. -/
theorem compatibleSimpleUnitization (ρ : A →ₙₐ[k] Module.End k M) :
    CompatibleSimpleUnitizationStatement ρ :=
  letI := module ρ
  (submoduleOrderIso ρ).isSimpleOrder_iff.trans (isSimpleModule_iff _ _).symm

/-- The original stable additive subgroup with the same carrier as a unitized submodule. -/
def unitizedNonUnitalSubmodule (ρ : A →ₙₐ[k] Module.End k M)
    (p : letI := module ρ; Submodule (Unitization k A) M) :
    letI := NonUnitalModule.ofLinearEndHom ρ; NonUnitalSubmodule A M :=
  letI := module ρ
  letI := NonUnitalModule.ofLinearEndHom ρ
  { toAddSubgroup := p.toAddSubgroup
    smul_mem' a m hm := by
      have h := p.smul_mem (a : Unitization k A) hm
      rw [inr_smul] at h
      exact h }

/-- Comparison 3: original additive simplicity implies simplicity of the unitized module. -/
theorem additiveSimpleUnitization (ρ : A →ₙₐ[k] Module.End k M) :
    AdditiveSimpleUnitizationStatement ρ := by
  rintro ⟨hnt, hS⟩
  let _inst := module ρ
  let _inst' := NonUnitalModule.ofLinearEndHom ρ
  have : Nontrivial (Submodule (Unitization k A) M) := (Submodule.nontrivial_iff _).2 hnt
  refine (isSimpleModule_iff _ _).2 ⟨fun p => ?_⟩
  rcases hS (unitizedNonUnitalSubmodule ρ p) with h | h
  · left
    refine (Submodule.eq_bot_iff p).2 fun m hm => ?_
    have hm' : m ∈ (unitizedNonUnitalSubmodule ρ p).toAddSubgroup := hm
    rw [h] at hm'
    exact AddSubgroup.mem_bot.1 hm'
  · right
    refine Submodule.eq_top_iff'.2 fun m => ?_
    have hm' : m ∈ (unitizedNonUnitalSubmodule ρ p).toAddSubgroup := by
      rw [h]
      exact AddSubgroup.mem_top m
    exact hm'

/-- The common annihilator `{m | ∀ a, ρ a m = 0}` of the original action, as a submodule of
the unitized action. -/
def annihilatorSubmodule (ρ : A →ₙₐ[k] Module.End k M) :
    letI := module ρ; Submodule (Unitization k A) M :=
  letI := module ρ
  { carrier := {m | ∀ a : A, ρ a m = 0}
    add_mem' {m n} hm hn a := by
      change ρ a (m + n) = 0
      rw [map_add, hm a, hn a, add_zero]
    zero_mem' a := map_zero (ρ a)
    smul_mem' x m hm a := by
      change ρ a (x.fst • m + ρ x.snd m) = 0
      rw [map_add, map_smul, hm a, smul_zero, zero_add]
      exact (LinearMap.congr_fun (map_mul ρ a x.snd) m).symm.trans (hm _) }

theorem mem_annihilatorSubmodule (ρ : A →ₙₐ[k] Module.End k M) {m : M} :
    (letI := module ρ; m ∈ annihilatorSubmodule ρ) ↔ ∀ a : A, ρ a m = 0 :=
  Iff.rfl

/-- The actual original orbit `{ρ a m | a ∈ A}`, as a submodule of the unitized action. -/
def orbitSubmodule (ρ : A →ₙₐ[k] Module.End k M) (m : M) :
    letI := module ρ; Submodule (Unitization k A) M :=
  letI := module ρ
  { carrier := Set.range fun a : A => ρ a m
    add_mem' := by
      rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change ρ (a + b) m = ρ a m + ρ b m
      rw [map_add, LinearMap.add_apply]
    zero_mem' := ⟨0, by
      change ρ 0 m = 0
      rw [map_zero, LinearMap.zero_apply]⟩
    smul_mem' := by
      rintro x _ ⟨a, rfl⟩
      refine ⟨x.fst • a + x.snd * a, ?_⟩
      change ρ (x.fst • a + x.snd * a) m = x.fst • ρ a m + ρ x.snd (ρ a m)
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_mul,
        Module.End.mul_apply] }

theorem mem_orbitSubmodule (ρ : A →ₙₐ[k] Module.End k M) {m n : M} :
    (letI := module ρ; n ∈ orbitSubmodule ρ m) ↔ ∃ a : A, ρ a m = n :=
  Iff.rfl

/-- Under unitized simplicity and `ρ ≠ 0`, the common annihilator is zero. -/
theorem annihilatorSubmodule_eq_bot (ρ : A →ₙₐ[k] Module.End k M) (hρ : ρ ≠ 0)
    (hs : letI := module ρ; IsSimpleModule (Unitization k A) M) :
    (letI := module ρ; annihilatorSubmodule ρ = ⊥) := by
  let _inst := module ρ
  rcases eq_bot_or_eq_top (annihilatorSubmodule ρ) with h | h
  · exact h
  · refine absurd ?_ hρ
    ext a n
    have hn : n ∈ annihilatorSubmodule ρ := h ▸ Submodule.mem_top
    rw [NonUnitalAlgHom.zero_apply, LinearMap.zero_apply]
    exact hn a

/-- Comparison 5 for one vector: under unitized simplicity and `ρ ≠ 0`, the original orbit map
of every nonzero vector is surjective. -/
theorem orbit_surjective (ρ : A →ₙₐ[k] Module.End k M) (hρ : ρ ≠ 0)
    (hs : letI := module ρ; IsSimpleModule (Unitization k A) M) {m : M} (hm : m ≠ 0) :
    Function.Surjective fun a : A => ρ a m := by
  let _inst := module ρ
  obtain ⟨a, ha⟩ : ∃ a : A, ρ a m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hm' : m ∈ annihilatorSubmodule ρ := hcon
    rw [annihilatorSubmodule_eq_bot ρ hρ hs] at hm'
    exact hm ((Submodule.mem_bot _).1 hm')
  rcases eq_bot_or_eq_top (orbitSubmodule ρ m) with h | h
  · refine absurd ?_ ha
    have ha' : ρ a m ∈ orbitSubmodule ρ m := ⟨a, rfl⟩
    rw [h] at ha'
    exact (Submodule.mem_bot _).1 ha'
  · intro n
    have hn : n ∈ orbitSubmodule ρ m := h ▸ Submodule.mem_top
    exact hn

/-- Comparison 5: under unitized simplicity and `ρ ≠ 0`, every nonzero vector has a surjective
original orbit map. -/
theorem simpleUnitizationOrbit (ρ : A →ₙₐ[k] Module.End k M) :
    SimpleUnitizationOrbitStatement ρ :=
  fun hρ hs _ hm => orbit_surjective ρ hρ hs hm

/-- Comparison 4: under `ρ ≠ 0`, unitized simplicity implies original additive simplicity. -/
theorem simpleUnitizationRestriction (ρ : A →ₙₐ[k] Module.End k M) :
    SimpleUnitizationRestrictionStatement ρ := by
  intro hρ hs
  let _inst := NonUnitalModule.ofLinearEndHom ρ
  refine ⟨(letI := module ρ; IsSimpleModule.nontrivial (Unitization k A) M), fun S => ?_⟩
  by_cases hS : S.toAddSubgroup = ⊥
  · exact Or.inl hS
  · right
    obtain ⟨m, hmS, hm0⟩ : ∃ m ∈ S.toAddSubgroup, m ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hS ((AddSubgroup.eq_bot_iff_forall _).2 hcon)
    refine (AddSubgroup.eq_top_iff' _).2 fun n => ?_
    obtain ⟨a, rfl⟩ := orbit_surjective ρ hρ hs hm0 n
    exact S.smul_mem' a hmS

/-- Comparison 6: under unitized simplicity and `ρ ≠ 0` of the source, every additive
original-action intertwiner preserves the specified field scalars. -/
theorem simpleUnitizationIntertwiner (ρ : A →ₙₐ[k] Module.End k M) :
    SimpleUnitizationIntertwinerStatement.{uK, uA, uM, uN} ρ := by
  intro hρ hs N _ _ σ f c m
  let _inst := NonUnitalModule.ofLinearEndHom ρ
  let _inst' := NonUnitalModule.ofLinearEndHom σ
  have : Nontrivial M := letI := module ρ; IsSimpleModule.nontrivial (Unitization k A) M
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  obtain ⟨a, rfl⟩ := orbit_surjective ρ hρ hs hm₀ m
  have hf : ∀ b : A, f (ρ b m₀) = σ b (f m₀) := fun b => f.map_smul' b m₀
  have hc : c • ρ a m₀ = ρ (c • a) m₀ := by rw [map_smul, LinearMap.smul_apply]
  change f (c • ρ a m₀) = c • f (ρ a m₀)
  rw [hc, hf, hf, map_smul, LinearMap.smul_apply]

end General

/-! ### The complex bridge -/

/-- Comparison 7: over the complex numbers, original additive simplicity implies `ρ ≠ 0`. -/
theorem complexAdditiveSimpleActionNonzero :
    ComplexAdditiveSimpleActionNonzeroStatement.{uA, uM} := by
  intro A _ _ _ _ M _ _ ρ hsimple hρ
  let _inst := NonUnitalModule.ofLinearEndHom ρ
  obtain ⟨hnt, hS⟩ := hsimple
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let S : NonUnitalSubmodule A M :=
    { toAddSubgroup := AddSubgroup.zmultiples m
      smul_mem' := fun a x _ => by
        change ρ a x ∈ AddSubgroup.zmultiples m
        rw [hρ, NonUnitalAlgHom.zero_apply, LinearMap.zero_apply]
        exact zero_mem _ }
  rcases hS S with h | h
  · apply hm
    have hm' : m ∈ S.toAddSubgroup := AddSubgroup.mem_zmultiples m
    rw [h] at hm'
    exact AddSubgroup.mem_bot.1 hm'
  · have hhalf : ((1 / 2 : ℂ) • m) ∈ S.toAddSubgroup := by
      rw [h]
      exact AddSubgroup.mem_top _
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hhalf
    rw [← Int.cast_smul_eq_zsmul ℂ] at hn
    have h2 : ((n : ℂ) - 1 / 2) • m = 0 := by rw [sub_smul, hn, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · have h4 : ((2 * n : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
        push_cast
        linear_combination 2 * h3
      have h5 : 2 * n = 1 := Int.cast_injective h4
      omega
    · exact hm h3

/-- The premise `ρ ≠ 0` of comparison 4 cannot be omitted: for the zero action of `ℂ` on `ℂ`,
the unitized module is simple, but the original action is not additively simple. -/
theorem zeroComplexAction_simple_not_additiveSimple :
    (letI := module (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ); IsSimpleModule (Unitization ℂ ℂ) ℂ) ∧
      ¬ (letI := NonUnitalModule.ofLinearEndHom (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ);
        (Nontrivial ℂ ∧ ∀ S : NonUnitalSubmodule ℂ ℂ,
          S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤)) := by
  refine ⟨?_, fun h => complexAdditiveSimpleActionNonzero 0 h rfl⟩
  let _inst := module (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)
  have _tower := isScalarTower (0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ)
  refine (isSimpleModule_iff _ _).2 ⟨fun p => ?_⟩
  rcases eq_bot_or_eq_top (p.restrictScalars ℂ) with h | h
  · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff _ _ _).1 h)
  · exact Or.inr ((Submodule.restrictScalars_eq_top_iff _ _ _).1 h)

/-! ### The aggregate -/

/-- The seven actual-action simplicity and scalar-linearity reductions. -/
theorem nonUnitalSimplicityReduction : NonUnitalSimplicityReductionStatement.{uK, uA, uM, uN} :=
  ⟨fun ρ => ⟨compatibleSimpleUnitization ρ, additiveSimpleCategorical ρ,
      additiveSimpleUnitization ρ, simpleUnitizationRestriction ρ, simpleUnitizationOrbit ρ,
      simpleUnitizationIntertwiner ρ⟩,
    complexAdditiveSimpleActionNonzero⟩

end CompatibleUnitization

end Langlands.Algebra
