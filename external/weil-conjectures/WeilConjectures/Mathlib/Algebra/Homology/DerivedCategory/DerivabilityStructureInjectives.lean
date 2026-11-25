/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# Morphisms from a single complex to a K-injective complex in `D⁺`

Let `M` be a bounded below complex which is K-injective, for instance a bounded below complex
of injective objects as produced by `DerivedCategory.Plus.exists_injective_nonempty_iso`. Every
morphism `A[0] ⟶ Q(M)` in `D⁺` comes from a morphism of complexes `A[0] ⟶ M`; its degree-`0`
homology is the map induced on cycles; and it vanishes if the morphism of complexes is
null-homotopic.

## Main statements

- `DerivedCategory.Plus.exists_ι_map_eq`: morphisms `A[0] ⟶ Q(M)` come from morphisms of
  complexes.
- `DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map`:
  their degree-`0` homology.
- `DerivedCategory.Plus.eq_zero_of_homotopy`: null-homotopic maps of complexes give zero.
-/

@[expose] public section

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

namespace Plus

/-- A morphism `A[0] ⟶ Q(M)` in `D⁺` with `M` K-injective comes from a morphism of complexes. -/
lemma exists_ι_map_eq {A : C} (M : CochainComplex.Plus C) [M.obj.IsKInjective]
    (β : (singleFunctor C 0).obj A ⟶ Q.obj M) :
    ∃ f : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ M.obj,
      ι.map β = DerivedCategory.Q.map f := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj ((HomologicalComplex.single C (.up ℤ) 0).obj A))
      M.obj).2 ((DerivedCategory.quotientCompQhIso C).hom.app _ ≫ ι.map β ≫
        (DerivedCategory.quotientCompQhIso C).inv.app M.obj)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨f, ?_⟩
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app _),
    ← quotientCompQhIso_hom_naturality, hg]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact congrArg ((DerivedCategory.quotientCompQhIso C).hom.app _ ≫ ·)
    (Category.comp_id (ι.map β)).symm

/-- The degree-`0` homology of a morphism `A[0] ⟶ Q(M)` coming from `f : A[0] ⟶ M`. -/
lemma singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map {A : C}
    {M : CochainComplex.Plus C} (β : (singleFunctor C 0).obj A ⟶ Q.obj M)
    (f : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ M.obj)
    (hf : ι.map β = DerivedCategory.Q.map f) :
    (singleFunctorCompHomologyFunctorIso 0).inv.app A ≫ (homologyFunctor C 0).map β =
      singleCyclesHom A ≫ HomologicalComplex.cyclesMap f 0 ≫ M.obj.homologyπ 0 ≫
        (homologyFunctorFactors C 0).inv.app M.obj := by
  change (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
    (DerivedCategory.homologyFunctor C 0).map (ι.map β) = _
  rw [hf, singleFunctorCompHomologyFunctorIso_inv_app_comp_map_Q_map]

/-- A morphism `A[0] ⟶ Q(M)` coming from a null-homotopic map of complexes is zero. -/
lemma eq_zero_of_homotopy {A : C} {M : CochainComplex.Plus C}
    (β : (singleFunctor C 0).obj A ⟶ Q.obj M)
    (f : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ M.obj)
    (hf : ι.map β = DerivedCategory.Q.map f)
    (h : Homotopy f 0) : β = 0 := by
  have h₀ : (HomotopyCategory.quotient _ _).map f = 0 := by
    rw [HomotopyCategory.eq_of_homotopy _ _ h, Functor.map_zero]
  have h₁ : DerivedCategory.Q.map f = 0 := by
    rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app _),
      ← quotientCompQhIso_hom_naturality, h₀]
    simp
  apply ι.map_injective
  rw [hf, h₁, Functor.map_zero]

end Plus

end DerivedCategory
