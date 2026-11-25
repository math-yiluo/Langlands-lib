/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.DirectSum.Basic
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Telescope

/-!
# Compact objects of an additive category with coproducts

Source: the blueprint of the Weil conjectures, chapter `chap-The-Picard-scheme-of-a-curve`, unit
`theorem-riemann-roch-coherent-serre-duality--2` (blueprint: def-pc-compact-object); Stacks Project,
Derived Categories, Definition 13.37.1 (Tag 09SM).

## Main statements

- `CategoryTheory.isCompactObject_iff_isCompactObj`: `IsCompactObject` agrees with
  `CategoryTheory.BrownRepresentability.IsCompactObj`, the notion used for Brown
  representability.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits DirectSum

namespace CategoryTheory

open Classical in
/-- (blueprint: def-pc-compact-object) Let `C` be an additive category with arbitrary coproducts.
An object `K` of `C` is *compact* if, for every set `I` and family `E : I → C`, the canonical map
`⨁ᵢ Hom(K, E i) → Hom(K, ⨁ᵢ E i)`, sending `f` in the `i`-th summand to `f ≫ Sigma.ι E i`, is
bijective (Stacks, Tag 09SM). The direct sum is taken with the classical decidable equality
on `I`. It is equivalent to `BrownRepresentability.IsCompactObj` by
`isCompactObject_iff_isCompactObj`. -/
def IsCompactObject {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (K : C) :
    Prop :=
  ∀ (I : Type w) (E : I → C),
    Function.Bijective
      (DirectSum.toAddMonoid (fun i : I => Preadditive.rightComp K (Sigma.ι E i)) :
        (⨁ i : I, (K ⟶ E i)) →+ (K ⟶ ∐ E))

section Compact

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{v} C]

open scoped Classical in
/-- The projection `∐ E ⟶ E j`, the identity on the summand `E j` and zero on the others. -/
private noncomputable def sigmaProj {I : Type v} (E : I → C) (j : I) : ∐ E ⟶ E j :=
  Sigma.desc (Pi.single (M := fun k : I ↦ E k ⟶ E j) j (𝟙 (E j)))

/-- The canonical map `⨁ Hom(K, E i) ⟶ Hom(K, ∐ E)` is injective in any preadditive category:
composing with the projection to `E j` recovers the `j`-th component. -/
private lemma toAddMonoid_comp_sigmaProj {I : Type v} [DecidableEq I] (E : I → C) (K : C)
    (d : ⨁ i : I, (K ⟶ E i)) (j : I) :
    DirectSum.toAddMonoid (fun i : I ↦ Preadditive.rightComp K (Sigma.ι E i)) d ≫
      sigmaProj E j = d j := by
  classical
  induction d using DirectSum.induction_on with
  | zero => simp
  | of k x =>
    rw [DirectSum.toAddMonoid_of]
    by_cases h : k = j
    · subst h
      simp [sigmaProj, Preadditive.rightComp]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      simp only [sigmaProj, Preadditive.rightComp, AddMonoidHom.mk'_apply, Category.assoc,
        Sigma.ι_comp_desc]
      convert comp_zero
      convert Pi.single_eq_of_ne h _
  | add d₁ d₂ h₁ h₂ => simp [Preadditive.add_comp, h₁, h₂]

/-- Compactness in the sense of `IsCompactObject` (bijectivity of
`⨁ Hom(K, E i) ⟶ Hom(K, ∐ E)`) agrees with `BrownRepresentability.IsCompactObj` (every
morphism to a coproduct is a finite sum of morphisms through the summands):
injectivity is automatic. -/
theorem isCompactObject_iff_isCompactObj (K : C) :
    IsCompactObject.{v} K ↔ BrownRepresentability.IsCompactObj K := by
  classical
  constructor
  · intro hK J X c hc f
    let e : c.pt ≅ ∐ X := hc.coconePointUniqueUpToIso (colimit.isColimit _)
    have he (j : J) : Sigma.ι X j ≫ e.inv = c.inj j :=
      hc.comp_coconePointUniqueUpToIso_inv (colimit.isColimit _) ⟨j⟩
    obtain ⟨d, hd⟩ := (hK J X).2 (f ≫ e.hom)
    refine ⟨d.support, fun j ↦ d j, ?_⟩
    rw [← cancel_mono e.hom, ← hd, DirectSum.toAddMonoid, DFinsupp.liftAddHom_apply]
    erw [DFinsupp.sumAddHom_apply]
    rw [DFinsupp.sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [Preadditive.rightComp, ← he]
  · intro hK I E
    refine ⟨(injective_iff_map_eq_zero _).2 fun d hd ↦ ?_, fun f ↦ ?_⟩
    · ext j
      rw [← toAddMonoid_comp_sigmaProj E K d j, hd, zero_comp]
      rfl
    · obtain ⟨S, g, hg⟩ := hK _ (coproductIsCoproduct E) f
      refine ⟨∑ j ∈ S, DirectSum.of (fun i ↦ K ⟶ E i) j (g j), ?_⟩
      simp [hg, Preadditive.rightComp]

end Compact

end CategoryTheory
