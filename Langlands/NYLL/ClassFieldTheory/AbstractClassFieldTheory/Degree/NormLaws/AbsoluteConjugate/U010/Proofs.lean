/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.Statements

/-!
# NYLL M026.010: the absolute norm commutes with conjugation

Modified by Worker 5264, 15 November 2026: prove the published target
`relativeNorm_absoluteConjugate_applyStatement` (M026.010) by the source
proof of `relativeNorm_absoluteConjugate_apply` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type and
begin the proof by unfolding it. Port the private source helper
`relativeCosetAction_absoluteConjugate` (M026.009) as a private theorem of
this module; since the source rewrites in its proof are with
`relativeCosetAction_mk` (published with a `...Statement` type) and with the
unpublished `rfl` lemmas M026.004 and M026.008, the port states the reduced
goal with `change` instead. In the main proof, the source
`simp only [relativeNorm_apply_coe, relativeNormValue]` is replaced by
`simp only [hcoe]` with a local fact `hcoe`, proved by `rfl`, that states the
coercion of `relativeNorm` over `baseField G` as the defining sum of
`relativeNormValue`; it is stated for the inclusion proof `le_baseField`
because that published theorem has the type `le_baseFieldStatement`, which
`simp` does not unfold when instantiating the general lemmas (the source
lemma M024.010 `relativeNorm_apply_coe` is also unpublished). Replace the
source imports by the published statement module and omit the unused opens
and the rest of the source file.
See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

private theorem relativeCosetAction_absoluteConjugate [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K)
    (q : (baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))) :
    relativeCosetAction A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) q =
      A.ρ σ⁻¹
        (relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
  refine Quotient.inductionOn' q ?_
  intro x
  change A.ρ x.1 (A.ρ σ⁻¹ a.1) = A.ρ σ⁻¹ (A.ρ (σ * x.1 * σ⁻¹) a.1)
  calc
    A.ρ x.1 (A.ρ σ⁻¹ a.1) = A.ρ (x.1 * σ⁻¹) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (σ⁻¹ * (σ * x.1 * σ⁻¹)) a.1 := by simp [mul_assoc]
    _ = A.ρ σ⁻¹ (A.ρ (σ * x.1 * σ⁻¹) a.1) := by
      rw [map_mul]
      rfl

/-- conjugation compatibility of normalized valuations: the absolute norm commutes with conjugation.

The construction writes the action on fields and elements on the right.  Thus the
left action used by `Rep` realizes `a^σ` as `ρ(σ⁻¹)a`. -/
theorem relativeNorm_absoluteConjugate_apply [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    [Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K))]
    (a : ambientFixedAddSubgroup A K) :
    relativeNorm_absoluteConjugate_applyStatement A K σ a := by
  unfold relativeNorm_absoluteConjugate_applyStatement
  have hcoe : ∀ (L' : ClosedSubgroup G)
      [Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) L' (le_baseField L'))]
      (b : ambientFixedAddSubgroup A L'),
      ((relativeNorm A (baseField G) L' (le_baseField L') b :
        ambientFixedAddSubgroup A (baseField G)) : A.V) =
        letI := Fintype.ofFinite ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) L' (le_baseField L'))
        ∑ q, relativeCosetAction A (baseField G) L' (le_baseField L') b q :=
    fun _ _ _ => rfl
  let := Fintype.ofFinite
    ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K
        (le_baseField K))
  let conjugateFintype : Fintype
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (conjugateClosedSubgroup K σ)
          (le_baseField (conjugateClosedSubgroup K σ))) :=
    Fintype.ofEquiv
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K))
      (absoluteConjugateCosetEquiv K σ).symm
  have hconjugateFintype : Fintype.ofFinite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (conjugateClosedSubgroup K σ)
          (le_baseField (conjugateClosedSubgroup K σ))) = conjugateFintype :=
    Subsingleton.elim _ _
  simp only [hcoe]
  rw [hconjugateFintype]
  calc
    ∑ q, relativeCosetAction A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) q =
      ∑ q, A.ρ σ⁻¹
        (relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
            apply Finset.sum_congr rfl
            intro q _
            exact relativeCosetAction_absoluteConjugate A K σ a q
    _ = A.ρ σ⁻¹
        (∑ q, relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
            rw [map_sum]
    _ = A.ρ σ⁻¹
        (∑ q, relativeCosetAction A (baseField G) K
          (le_baseField K) a q) := by
            rw [(absoluteConjugateCosetEquiv K σ).sum_comp]

end

end Langlands.NYLL.ClassFormation
