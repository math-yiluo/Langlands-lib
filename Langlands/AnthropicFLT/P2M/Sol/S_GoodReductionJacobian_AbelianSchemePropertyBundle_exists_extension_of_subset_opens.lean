/-
Ported from `P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_extension_of_subset_opens.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension
import Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_extension_of_subset_opens
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ φ : SchemeHomOver t f, V.ι ≫ φ.1 = v.1 := by
  obtain ⟨G⟩ := hA.hasGroupLaw
  haveI : Smooth f := hA.smooth
  haveI : IsSeparated f := hA.proper.toIsSeparated
  obtain ⟨W, d, hd⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension R G t V hVη hVs v
  exact GoodReductionJacobian.RelativeGroupLaw.exists_extension_of_diagonal_difference_extension R G t V hVη hVs v W d hd
