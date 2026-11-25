/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Derived bifunctor restriction to resolving pairs

Source: Stacks Project, categories.tex, localization universal property.
(blueprint: lem-pur-derived-resolving-pair-restriction).
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

/-- Restriction to pairs of resolving cochain complexes detects and lifts natural
transformations of derived bifunctors.
Source: Stacks Project, categories.tex, localization universal property;
localization through the homotopy category and resolving-representative restriction.
(blueprint: lem-pur-derived-resolving-pair-restriction).

Proof: put the resolving predicate on the underlying complexes of homotopy objects.
A resolving quasi-isomorphism of complexes maps to such a homotopy morphism. Apply
fully faithful restriction for resolving homotopy representatives, then transport
along the canonical quotientCompQhIso in both variables. -/
theorem derivedResolvingPairRestriction
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (B : Type*) [Category B] (P : ObjectProperty (CochainComplex A ℤ))
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (L : CochainComplex A ℤ) (a : L ⟶ K), P L ∧ QuasiIso a) :
    Nonempty (((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (DerivedCategory A × DerivedCategory A) B).obj
        ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let H : ObjectProperty
      (HomotopyCategory A (.up ℤ)) := fun K ↦ P K.as
  have hres : ∀ K : HomotopyCategory A (.up ℤ),
      ∃ (L : H.FullSubcategory) (a : L.obj ⟶ K),
        HomotopyCategory.quasiIso A (.up ℤ) a := by
    intro K
    obtain ⟨L, a, hL, ha⟩ := res K.as
    exact ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj L, hL⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map a,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff a).2 ha⟩
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering B
    (HomotopyCategory.quotient _ (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh
    P H (fun _ ↦ Iff.rfl) hres
  exact ⟨ff.ofIso ((Functor.whiskeringLeft _ _ B).mapIso
    (NatIso.prod (isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso
        A))
      (isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso
        A))))⟩

end CategoryTheory
