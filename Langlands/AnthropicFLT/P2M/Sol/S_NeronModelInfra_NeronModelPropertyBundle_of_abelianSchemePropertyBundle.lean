/-
Ported from `P2M/Sol/S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_genericFibreRestrict_surjective_of_quasiCompact
import Langlands.AnthropicFLT.Theorems.Thm_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f) :
    NeronModelInfra.NeronModelPropertyBundle R K f := by
  haveI : IsProper f := hA.proper
  have hsep : IsSeparated f := inferInstance
  refine ⟨hA.smooth, hsep, inferInstance, inferInstance, ?_⟩
  refine neronUniqueExtension_of_forall_quasiCompact R K f fun T t ht hqc => ?_
  haveI := ht
  haveI := hqc
  haveI : Flat t := inferInstance
  exact ⟨genericFibreRestrict_injective_of_flat_of_isSeparated R K f t,
    hA.genericFibreRestrict_surjective_of_quasiCompact R K t⟩
