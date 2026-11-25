/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import WeilConjectures.Algebra.Homology.HopfTrace
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectTrace

/-!
# Formal laws of the trace on perfect complexes

This file proves two of the formal laws of blueprint `proposition-properties-trace`
(subsection `proposition-properties-trace`) for the categorical trace in the derived category
`D(R)`, with the Koszul braiding `DerivedCategory.braidedCategory'` of the derived tensor product.

## Main results

- `DerivedCategory.trace_eq_trace_add_trace_of_shortExact`, item (2) (filtered additivity), in
  the short exact sequence form: for a short exact sequence `0 → P' → P → P'' → 0` of bounded
  complexes of finitely generated free `R`-modules and an endomorphism `(v', v, v'')` of it,
  `tr (v ∣ P) = tr (v' ∣ P') + tr (v'' ∣ P'')`.
- `DerivedCategory.trace_eq_algebraMap_sum_negOnePow_trace_homologyMap`, item (4) (supertrace
  over a field): for a field `Λ` and a bounded complex `P` of finite dimensional vector spaces,
  `tr_Λ (v ∣ P) = ∑ i, (-1) ^ i * Tr (H ^ i (v) ∣ H ^ i (P))`.

Both are reduced, through `DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace`, to
linear algebra: the additivity of the trace along short exact sequences of finite free modules
(`LinearMap.trace_eq_trace_add_trace_of_exact`) and the Hopf trace formula
(`CochainComplex.sum_negOnePow_smul_trace_f_eq_sum_negOnePow_smul_trace_homologyMap`).

## Implementation notes

As in `DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace`, dualizability of the
complexes is rendered by objects `K` of `D(R)` with `[HasRightDual K]` and isomorphisms
`e : K ≅ Q.obj P` intertwining the endomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

section Additivity

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
  [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]

/-- Blueprint `proposition-properties-trace`, item (2) (filtered additivity), for a triangle coming
from a short exact sequence: let `0 → P' → P → P'' → 0` be a short exact sequence `S` of bounded
complexes of `R`-modules with `P'` and `P''` (hence also `P`) degreewise finitely generated and
free, and let `φ = (v', v, v'')` be an endomorphism of `S`. Then the categorical traces in `D(R)`
satisfy `tr (v ∣ P) = tr (v' ∣ P') + tr (v'' ∣ P'')`. -/
theorem trace_eq_trace_add_trace_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) (φ : S ⟶ S)
    (s : Finset ℤ) (hs : ∀ i ∉ s, IsZero (S.X₂.X i))
    (hfree₁ : ∀ i, Module.Free R (S.X₁.X i)) (hfin₁ : ∀ i, Module.Finite R (S.X₁.X i))
    (hfree₃ : ∀ i, Module.Free R (S.X₃.X i)) (hfin₃ : ∀ i, Module.Finite R (S.X₃.X i))
    (K₁ K₂ K₃ : DerivedCategory (ModuleCat.{u} R)) [HasRightDual K₁] [HasRightDual K₂]
    [HasRightDual K₃] (w₁ : K₁ ⟶ K₁) (w₂ : K₂ ⟶ K₂) (w₃ : K₃ ⟶ K₃)
    (e₁ : K₁ ≅ Q.obj S.X₁) (e₂ : K₂ ≅ Q.obj S.X₂) (e₃ : K₃ ≅ Q.obj S.X₃)
    (hw₁ : w₁ ≫ e₁.hom = e₁.hom ≫ Q.map φ.τ₁) (hw₂ : w₂ ≫ e₂.hom = e₂.hom ≫ Q.map φ.τ₂)
    (hw₃ : w₃ ≫ e₃.hom = e₃.hom ≫ Q.map φ.τ₃) :
    letI := braidedCategory' (ModuleCat.{u} R)
    MonoidalCategory.trace w₂ = MonoidalCategory.trace w₁ + MonoidalCategory.trace w₃ := by
  let := braidedCategory' (ModuleCat.{u} R)
  have hS' (i : ℤ) := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i
  have hexact (i : ℤ) : Function.Exact (S.f.f i) (S.g.f i) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS' i).exact
  have hinj (i : ℤ) : Function.Injective (S.f.f i) := (hS' i).moduleCat_injective_f
  have hsurj (i : ℤ) : Function.Surjective (S.g.f i) := (hS' i).moduleCat_surjective_g
  have hfree₂ (i : ℤ) : Module.Free R (S.X₂.X i) :=
    Module.Free.of_exact (hexact i) (hinj i) (hsurj i)
  have hfin₂ (i : ℤ) : Module.Finite R (S.X₂.X i) := Module.Finite.of_exact (hexact i) (hsurj i)
  have hs₁ (i : ℤ) (hi : i ∉ s) : IsZero (S.X₁.X i) := by
    have := ModuleCat.subsingleton_of_isZero (hs i hi)
    exact ModuleCat.isZero_iff_subsingleton.2 ⟨fun x y ↦ hinj i (Subsingleton.elim _ _)⟩
  have hs₃ (i : ℤ) (hi : i ∉ s) : IsZero (S.X₃.X i) := by
    have := ModuleCat.subsingleton_of_isZero (hs i hi)
    refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun x y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hsurj i x
    obtain ⟨y, rfl⟩ := hsurj i y
    rw [Subsingleton.elim x y]
  rw [trace_eq_algebraMap_sum_negOnePow_linearMapTrace S.X₁ φ.τ₁ s hs₁ hfree₁ hfin₁ K₁ w₁ e₁ hw₁,
    trace_eq_algebraMap_sum_negOnePow_linearMapTrace S.X₂ φ.τ₂ s hs hfree₂ hfin₂ K₂ w₂ e₂ hw₂,
    trace_eq_algebraMap_sum_negOnePow_linearMapTrace S.X₃ φ.τ₃ s hs₃ hfree₃ hfin₃ K₃ w₃ e₃ hw₃]
  refine congrArg End.asHom
    ((congrArg (algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u} R))))) ?_).trans
      (map_add _ _ _))
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← smul_add]
  exact congrArg _ (LinearMap.trace_eq_trace_add_trace_of_exact (hexact i) (hinj i) (hsurj i)
    (congrArg ModuleCat.Hom.hom (HomologicalComplex.congr_hom φ.comm₁₂ i)).symm
    (congrArg ModuleCat.Hom.hom (HomologicalComplex.congr_hom φ.comm₂₃ i)))

end Additivity
section Field

variable {Λ : Type u} [Field Λ] [HasDerivedCategory.{u} (ModuleCat.{u} Λ)]
  [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} Λ)]

/-- Blueprint `proposition-properties-trace`, item (4) (supertrace over a field): for a field `Λ`,
a bounded complex `P` of finite dimensional `Λ`-vector spaces and a chain endomorphism `v` of `P`,
the categorical trace of `v` on the object of `D(Λ)` represented by `P` is the alternating sum of
the traces of the maps induced by `v` on homology:

`tr_Λ (v ∣ P) = ∑ i, (-1) ^ i * Tr (H ^ i (v) ∣ H ^ i (P))`. -/
theorem trace_eq_algebraMap_sum_negOnePow_trace_homologyMap
    (P : CochainComplex (ModuleCat.{u} Λ) ℤ) (v : P ⟶ P) (s : Finset ℤ)
    (hs : ∀ i ∉ s, IsZero (P.X i)) (hfin : ∀ i, Module.Finite Λ (P.X i))
    (K : DerivedCategory (ModuleCat.{u} Λ)) [HasRightDual K] (w : K ⟶ K)
    (e : K ≅ Q.obj P) (hw : w ≫ e.hom = e.hom ≫ Q.map v) :
    letI := braidedCategory' (ModuleCat.{u} Λ)
    MonoidalCategory.trace w =
      (algebraMap Λ (End (𝟙_ (DerivedCategory (ModuleCat.{u} Λ))))
        (∑ i ∈ s, (i.negOnePow : ℤ) •
          LinearMap.trace Λ (P.homology i) (HomologicalComplex.homologyMap v i).hom)).asHom := by
  rw [trace_eq_algebraMap_sum_negOnePow_linearMapTrace P v s hs (fun _ ↦ inferInstance) hfin K w e
    hw, CochainComplex.sum_negOnePow_smul_trace_f_eq_sum_negOnePow_smul_trace_homologyMap P v s hs
    hfin]

end Field

end DerivedCategory
