/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact

/-! # Exact extension by zero and restriction on a ringed space

Source: literature/stacks-project/cohomology.tex, Lemma 08BS (proof), citing
literature/stacks-project/sheaves.tex, Lemma 00A7 and
literature/stacks-project/modules.tex, Lemma 01AK
(blueprint: lem-sc-derived-open-restriction-adjunction-exact).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For an open `U` of a ringed space `X`, restriction
`j⁻¹ = SheafOfModules.overFunctor (moduleRings X) U : Mod(O_X) ⥤ Mod(O_U)` is exact, and
extension by zero `j_!` (the extension-by-zero presheaf followed by module
sheafification) is exact and left adjoint to it: `j_! ⊣ j⁻¹`. Exactness is preservation
of finite limits and finite colimits.

Source: literature/stacks-project/cohomology.tex, Lemma 08BS, with
Sheaves Lemma 00A7 and Modules Lemma 01AK
(blueprint: lem-sc-derived-open-restriction-adjunction-exact).

Proof: (1) Exactness of `j⁻¹` is checked stalkwise
(`lem-weil-pbc-module-stalk-exact` (5)): the stalk of a restriction at `x ∈ U` is the
stalk at `x`. (2) The adjunction: a presheaf map from the extension-by-zero presheaf to
`G` is a map on `U` (extend by zero outside `U`), and composing with the universal
property of module sheafification (`def-weil-presheaf-modules-sheafification`) gives
`j_! ⊣ j⁻¹`. (3) Exactness of `j_!`: its stalk at `x ∈ U` is the stalk of the input and
at `x ∉ U` is zero (`lem-weil-pbc-stalk-sheafification-space`), so it is exact by
`lem-weil-pbc-module-stalk-exact` (5). -/
theorem open_restriction_adjunction_exact (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) ∧
      PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) ∧
      PreservesFiniteLimits
        (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)) ∧
      PreservesFiniteColimits
        (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)) ∧
      Nonempty
        (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj) ⊣
          SheafOfModules.overFunctor.{u} (moduleRings X) U) := by
  -- Specialize the localized ringed-site theorem (Stacks, Tags 03DI and 03DJ).
  -- The covering precoverage generates the original topology, so both module
  -- categories and the extension-by-zero construction are the stated ones.
  have hJ : (Opens.grothendieckTopology X).toPrecoverage.toGrothendieck =
      Opens.grothendieckTopology X := by
    apply le_antisymm
    · exact GrothendieckTopology.toGrothendieck_toPrecoverage_le _
    · intro V S hS
      simpa only [Sieve.generate_sieve] using
        Precoverage.generate_mem_toGrothendieck
          ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ S).mpr hS)
  let P (J : GrothendieckTopology (Opens X)) (O : Sheaf J CommRingCat.{u}) :=
    let R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} R U) ∧
      PreservesFiniteColimits (SheafOfModules.overFunctor.{u} R U) ∧
      PreservesFiniteLimits (SheafOfModules.extensionByZeroPresheaf.{u} R U ⋙
        PresheafOfModules.sheafification.{u} (𝟙 R.obj)) ∧
      PreservesFiniteColimits (SheafOfModules.extensionByZeroPresheaf.{u} R U ⋙
        PresheafOfModules.sheafification.{u} (𝟙 R.obj)) ∧
      Nonempty (SheafOfModules.extensionByZeroPresheaf.{u} R U ⋙
        PresheafOfModules.sheafification.{u} (𝟙 R.obj) ⊣
          SheafOfModules.overFunctor.{u} R U)
  change P (Opens.grothendieckTopology X) X.sheaf
  have h : ∀ O, P (Opens.grothendieckTopology X) O := by
    rw [← hJ]
    intro O
    exact SheafOfModules.localizedModule_adjunction_exact
      (Opens.grothendieckTopology X).toPrecoverage O U
  exact h X.sheaf

end AlgebraicGeometry
