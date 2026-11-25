/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.LocalSectionOfEpi
import WeilConjectures.AlgebraicGeometry.Modules.DualRetractionOfLocalSection

/-!
# Local splitting of the transpose of an epimorphism

The transpose `Qᵛ ⟶ Pᵛ` of an epimorphism `P ⟶ Q` onto a finite locally free module is locally
a split monomorphism.

## References

* [Stacks: Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The transpose of an epimorphism onto a finite locally free module is locally split. -/
theorem exists_local_retraction_dualMap_of_epi
    {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q) [Epi f] [Q.IsFiniteLocallyFree] :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map (dualMap f)) := by
  intro x
  obtain ⟨U, hxU, s, hs⟩ := exists_local_section_of_epi f x
  exact ⟨U, hxU, isSplitMono_restrict_dualMap_of_local_section f U s hs⟩

end AlgebraicGeometry.Scheme.Modules
