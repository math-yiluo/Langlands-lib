/-
Ported from `P2M/Sol/S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Theorems.Thm_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field
import Langlands.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_mvPolynomial
import Langlands.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_of_etale_of_comap
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

theorem solution
    (k B : Type*) [Field k] [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmooth k B] (q : Ideal B) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  obtain ⟨m, hm⟩ :=
    Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_of_field (k := k) (B := B)
  haveI := hm
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial m k B
  letI : Algebra (MvPolynomial (Fin m) k) B := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin m) k) B := hg
  haveI : IsScalarTower k (MvPolynomial (Fin m) k) B :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have hbase := isRegularLocalRing_localization_atPrime_mvPolynomial k m
    (q.comap (algebraMap (MvPolynomial (Fin m) k) B))
  exact isRegularLocalRing_localization_atPrime_of_etale_of_comap
    (MvPolynomial (Fin m) k) B q hbase
