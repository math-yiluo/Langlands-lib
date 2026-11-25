/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-! Sectionwise injectivity input for the proper/open counit.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (A : Type u) [CommRing A] [Finite A]

/-- After forgetting the ring action, the proper/open counit (the counit of the
extension-by-zero adjunction for `i` at `p_* i'_! M`) is a monomorphism. -/
theorem sfProperOpenCounit_forget_mono {V W T : Scheme.{u}} (p : V ⟶ T) [IsProper p]
    (i : W ⟶ T) [IsOpenImmersion i] (M :
      proEtaleRingModules (pullback p i)
        (proEtaleConstantRing (pullback p i) A)) :
    Mono ((SheafOfModules.forget
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing T A))).map
      ((sfIntrinsicExtensionByZeroAdjunction i A).counit.app
        ((sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
          proEtaleConstantModuleDirectImage p A).obj M))) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have hmono (N : Sheaf (ProEt.topology T) B) :
      Mono ((ProEtale.openImmersionLowerShriekAdjunction B i).counit.app N) := by
    apply ProEtale.mono_of_mono_openImmersionLowerShriekAdjunction_unit_app_comp B i
    rw [Adjunction.right_triangle_components]
    exact ⟨fun _ _ h ↦ by simpa using h⟩
  have (N : proEtaleRingModules T (proEtaleConstantRing T A)) :
      Mono ((sfIntrinsicExtensionByZeroAdjunction i A).counit.app N) := by
    dsimp only [sfIntrinsicExtensionByZeroAdjunction]
    rw [Adjunction.comp_counit_app, Adjunction.comp_counit_app]
    infer_instance
  infer_instance

end AlgebraicGeometry.Scheme
