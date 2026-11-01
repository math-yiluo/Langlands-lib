import Langlands.Algebra.NonUnitalModuleDualExactnessStatements
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Exactness of actual dual pullbacks by full-dual extension and idempotent projection. -/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open MulOpposite

universe uA uM uN uP

namespace NonUnitalModuleDual

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)

local instance mapExactnessFullActionM :
    NonUnitalModule Aᵐᵒᵖ (FullDual hA hM) := fullAction hA hM
local instance mapExactnessFullActionN :
    NonUnitalModule Aᵐᵒᵖ (FullDual hA hN) := fullAction hA hN

/-- A lift in the full dual can be projected to an actual nondegenerate lift. -/
theorem pullback_lift_of_full (f : NonUnitalModuleHom A M N)
    (φ : Dual hA hM) (ψ : FullDual hA hN)
    (hψ : ∀ m : M, ψ (f m) = φ.val m) :
    ∃ ψ' : Dual hA hN, pullback hA hM hN f ψ' = φ := by
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NondegenerateScalars.complexModule hA hN
  obtain ⟨e, he⟩ := (mem_dual_iff hA hM φ.val).1 φ.property
  let ψ' : Dual hA hN := ⟨op (e : A) • ψ,
    (mem_dual_iff hA hN _).2 ⟨e, by
      intro n
      change ψ ((e : A) • ((e : A) • n)) = ψ ((e : A) • n)
      rw [← mul_smul, e.property.eq]⟩⟩
  refine ⟨ψ', ?_⟩
  apply dual_ext hA hM
  intro m
  change ψ ((e : A) • f m) = φ.val m
  rw [← f.map_smul, hψ, he]

/-- Injective original maps give surjective actual dual pullbacks. -/
theorem pullback_surjective_of_injective (f : NonUnitalModuleHom A M N)
    (hf : Function.Injective f) : Function.Surjective (pullback hA hM hN f) := by
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NondegenerateScalars.complexModule hA hN
  intro φ
  obtain ⟨ψ, hψ⟩ := LinearMap.dualMap_surjective_of_injective
    (f := NondegenerateScalars.complexToLinearMap hA hM hN f) hf φ.val
  exact pullback_lift_of_full hA hM hN f φ ψ
    (fun m => congrArg (fun η : FullDual hA hM => η m) hψ)

/-- Surjective original maps give injective actual dual pullbacks. -/
theorem pullback_injective_of_surjective (f : NonUnitalModuleHom A M N)
    (hf : Function.Surjective f) : Function.Injective (pullback hA hM hN f) := by
  intro φ ψ h
  apply dual_ext hA hN
  intro n
  obtain ⟨m, rfl⟩ := hf n
  exact congrArg (fun η : Dual hA hM => η.val m) h

variable {P : Type uP} [AddCommGroup P] [NonUnitalModule A P]
  (hP : IsNondegenerate A P)

local instance mapExactnessFullActionP :
    NonUnitalModule Aᵐᵒᵖ (FullDual hA hP) := fullAction hA hP

/-- Exact original pairs give exact actual dual pairs, with independent universes. -/
theorem pullback_exact (f : NonUnitalModuleHom A M N) (g : NonUnitalModuleHom A N P)
    (hfg : Function.Exact f g) :
    Function.Exact (pullback hA hN hP g) (pullback hA hM hN f) := by
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NondegenerateScalars.complexModule hA hN
  let _ := NondegenerateScalars.complexModule hA hP
  intro φ
  constructor
  · intro hφ
    have hker : φ.val ∈
        (LinearMap.ker (NondegenerateScalars.complexToLinearMap hA hN hP g)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro n hn
      obtain ⟨m, rfl⟩ := (hfg n).1 hn
      exact congrArg (fun η : Dual hA hM => η.val m) hφ
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hker
    obtain ⟨ψ, hψ⟩ := hker
    exact pullback_lift_of_full hA hN hP g φ ψ
      (fun n => congrArg (fun η : FullDual hA hN => η n) hψ)
  · rintro ⟨ψ, rfl⟩
    apply dual_ext hA hM
    intro m
    change ψ.val (g (f m)) = 0
    rw [hfg.apply_apply_eq_zero, map_zero]

end NonUnitalModuleDual

/-- The exact four-universe original-map target. -/
theorem nonUnitalModuleDualMapExactnessStatement :
    NonUnitalModuleDualMapExactnessStatement.{uA, uM, uN, uP} := by
  intro A _ _ _ _ hA M _ _ N _ _ P _ _ hM hN hP f g
  let _ := NonUnitalModuleDual.fullAction hA hM
  let _ := NonUnitalModuleDual.fullAction hA hN
  let _ := NonUnitalModuleDual.fullAction hA hP
  refine ⟨NonUnitalModuleDual.pullback_exact hA hM hN hP f g,
    NonUnitalModuleDual.pullback_surjective_of_injective hA hM hN f,
    NonUnitalModuleDual.pullback_injective_of_surjective hA hM hN f, ?_⟩
  rintro ⟨hf, hfg, hg⟩
  exact ⟨NonUnitalModuleDual.pullback_injective_of_surjective hA hN hP g hg,
    NonUnitalModuleDual.pullback_exact hA hM hN hP f g hfg,
    NonUnitalModuleDual.pullback_surjective_of_injective hA hM hN f hf⟩

example : NonUnitalModuleDualMapExactnessStatement.{uA, uM, uN, uP} :=
  @nonUnitalModuleDualMapExactnessStatement.{uA, uM, uN, uP}

example : NonUnitalModuleDualMapExactnessStatement.{0, 1, 2, 3} :=
  @nonUnitalModuleDualMapExactnessStatement.{0, 1, 2, 3}

example : NonUnitalModuleDualMapExactnessStatement.{3, 0, 2, 1} :=
  @nonUnitalModuleDualMapExactnessStatement.{3, 0, 2, 1}

end Langlands.Algebra
