/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenCounitMonoSection

/-! Monomorphism half of the proper/open pro-etale counit support argument.

## References

* Stacks, Tags 09AE and 09AG
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- For `p` proper and `i` an open immersion, the counit of the extension-by-zero adjunction
for `i` at `p_* i'_! M` is a monomorphism, where `i'` is the base change of `i`. -/
theorem sfProperOpenCounit_mono {V W T : Scheme.{u}} (p : V ⟶ T) [IsProper p]
    (i : W ⟶ T) [IsOpenImmersion i] (M :
      proEtaleRingModules (pullback p i)
        (proEtaleConstantRing (pullback p i) A)) :
    Mono ((sfIntrinsicExtensionByZeroAdjunction i A).counit.app
      ((sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
        proEtaleConstantModuleDirectImage p A).obj M)) := by
  apply Functor.mono_of_mono_map (SheafOfModules.forget
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing T A)))
  exact sfProperOpenCounit_forget_mono A p i M

end AlgebraicGeometry.Scheme
