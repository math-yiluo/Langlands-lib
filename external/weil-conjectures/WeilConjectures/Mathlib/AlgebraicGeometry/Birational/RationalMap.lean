/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!
# Extending rational maps over valuation rings

Let `X` be an integral `S`-scheme all of whose local rings are valuation rings (e.g. a regular
curve), and `Y` a proper separated `S`-scheme, `S` separated. Then every `S`-morphism
`Spec K(X) ⟶ Y` extends to an `S`-morphism `X ⟶ Y`: by the valuative criterion it extends to
`Spec 𝒪_{X,x}` for each point `x`, so `x` lies in the domain of definition of the corresponding
rational map.

## Main statements

- `AlgebraicGeometry.Scheme.exists_hom_of_valuationRing_stalk`: the extension.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X Y S : Scheme.{u}} [X.Over S] [Y.Over S]

/-- **Extension of rational maps over valuation rings.** If `X` is integral with all local rings
valuation rings and `Y` is proper and separated over `S`, every `S`-morphism `Spec K(X) ⟶ Y`
extends to an `S`-morphism `X ⟶ Y`. -/
theorem exists_hom_of_valuationRing_stalk [IsIntegral X] [IsProper (Y ↘ S)] [Y.IsSeparated]
    [S.IsSeparated]
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (g : Spec X.functionField ⟶ Y)
    (hg : g ≫ Y ↘ S = X.fromSpecFunctionField ≫ X ↘ S) :
    ∃ π : X ⟶ Y, π.IsOver S ∧ X.fromSpecFunctionField ≫ π = g := by
  let f : X ⤏ Y := RationalMap.ofFunctionField (X ↘ S) (Y ↘ S) g hg
  have hf : f.fromFunctionField = g := RationalMap.fromFunctionField_ofFunctionField _ _ _ _
  have hdom : f.domain = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have hdom : IsDomain (X.presheaf.stalk x) := inferInstance
    have := hX x
    have hsq : CommSq g (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        X.functionField))) (Y ↘ S) (X.fromSpecStalk x ≫ X ↘ S) := ⟨by
      rw [hg, ← Category.assoc]
      congr 1
      exact (SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)).symm⟩
    have hval : ValuativeCriterion.Existence (Y ↘ S) :=
      (UniversallyClosed.eq_valuativeCriterion ▸
        (inferInstance : UniversallyClosed (Y ↘ S))).1
    obtain ⟨⟨l, hl₁, hl₂⟩⟩ := hval
      { R := X.presheaf.stalk x, domain := hdom, K := X.functionField, i₁ := g,
        i₂ := X.fromSpecStalk x ≫ X ↘ S, commSq := hsq }
    let p := PartialMap.ofFromSpecStalk (X ↘ S) (Y ↘ S) l (by rw [hl₂])
    have hp : x ∈ p.domain := PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
    refine RationalMap.mem_domain.mpr ⟨p, hp, RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
    rw [hf, RationalMap.fromFunctionField_toRationalMap]
    refine Eq.trans ?_ hl₁
    have h₁ : p.fromSpecStalkOfMem hp = l :=
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk (X ↘ S) (Y ↘ S) l (by rw [hl₂])
    change _ = _ ≫ l
    rw [← h₁]
    simp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem, ← Category.assoc]
    congr 1
    rw [← cancel_mono p.domain.ι, Category.assoc, Opens.fromSpecStalkOfMem_ι,
      Opens.fromSpecStalkOfMem_ι]
    exact (SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)).symm
  let P := f.toPartialMap
  have hP : P.domain = ⊤ := hdom
  have : IsIso P.domain.ι := Opens.isIso_ι_of_eq_top hP
  have : f.IsOver S := by
    rw [RationalMap.isOver_iff]
    exact ((RationalMap.equivFunctionField (X ↘ S) (Y ↘ S)) ⟨g, hg⟩).2
  have h₁ : P.hom ≫ Y ↘ S = P.domain.ι ≫ X ↘ S := PartialMap.isOver_iff.mp inferInstance
  refine ⟨inv P.domain.ι ≫ P.hom, ⟨?_⟩, ?_⟩
  · rw [Category.assoc, h₁, IsIso.inv_hom_id_assoc]
  · have hmem : genericPoint X ∈ P.domain := hP ▸ trivial
    have h₂ : X.fromSpecFunctionField ≫ inv P.domain.ι =
        P.domain.fromSpecStalkOfMem (genericPoint X) hmem := by
      rw [IsIso.comp_inv_eq, Opens.fromSpecStalkOfMem_ι]
    rw [← Category.assoc, h₂, ← hf, ← f.toRationalMap_toPartialMap,
      RationalMap.fromFunctionField_toRationalMap]
    rfl

end AlgebraicGeometry.Scheme
