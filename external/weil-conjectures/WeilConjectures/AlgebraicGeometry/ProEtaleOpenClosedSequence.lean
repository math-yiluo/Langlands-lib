/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # The pro-étale open-closed sequence

The proof uses the existing module-valued closed-counit, disjoint-support and
joint-conservativity theorems. Exact restriction to the complementary open and closed
subschemes identifies the sequence with split short exact sequences.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The open-closed localization sequence is short exact.
Source: Stacks Project, Tag 09AH (auxiliary; not a blueprint node).

Proof: restriction to the open identifies the sequence with the split sequence
`F|U → F|U → 0`, using full faithfulness of extension by zero. Restriction to the
closed identifies it with `0 → F|Z → F|Z`, using the closed-immersion counit.
Both inverse images are exact and together detect zero objects: an object vanishing
on the open is supported on the closed and is the direct image of its closed
restriction. They therefore detect monomorphisms, epimorphisms and exactness.
-/
theorem exact_openClosedSequence (Λ : Type (u + 1)) [CommRing Λ]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    Mono ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F) ∧
      Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F) ∧
      (ComposableArrows.mk₂
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F)
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F)).Exact := by
  let A := ModuleCat.{u + 1} Λ
  let a := openImmersionLowerShriekUpperStarAdjunction A j
  let b := upperStarLowerStarAdjunction A i
  have hij : IsCompl (Set.range i.base) (Set.range j.base) :=
    compl_eq_iff_isCompl.mp hU.symm
  have hz (M : Sheaf (ProEt.topology Z) A) :
      IsZero (((j)^*[A]).obj (((i)_*[A]).obj M)) :=
    isZero_upperStar_lowerStar_of_disjoint A i j hij.disjoint M
  have hzi (M : Sheaf (ProEt.topology U) A) :
      IsZero (((i)^*[A]).obj ((openImmersionLowerShriek A j).obj M)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (b.homEquiv _ _).injective
    apply (a.homEquiv _ _).injective
    exact (hz _).eq_of_tgt _ _
  have hzero : a.counit.app F ≫ b.unit.app F = 0 := by
    apply (a.homEquiv _ _).injective
    exact (hz _).eq_of_tgt _ _
  let Q := ShortComplex.mk (a.counit.app F) (b.unit.app F) hzero
  have hreflect : JointlyReflectIsomorphisms (pairFunctor ((j)^*[A]) ((i)^*[A])) :=
    jointlyReflectIsomorphisms_pairFunctor _ _ fun _ _ φ hj hi ↦ by
      have := hj
      have := hi
      exact isIso_of_isIso_upperStar_of_isCompl i j hij φ
  have hQ : Q.ShortExact := by
    rw [hreflect.shortExact_iff]
    rintro (_ | _)
    · have hc : IsIso b.counit := isIso_upperStarLowerStarAdjunction_counit (ModuleCat.{u + 1} Λ) i
      have hgi : IsIso (((i)^*[A]).map (b.unit.app F)) := by
        have h := b.left_triangle_components F
        rw [← IsIso.inv_eq_of_inv_hom_id h]
        infer_instance
      have : IsIso ((Q.map ((i)^*[A])).g) := hgi
      have hfi : (Q.map ((i)^*[A])).f = 0 := (hzi _).eq_of_src _ _
      exact
        { exact := (ShortComplex.exact_iff_mono _ hfi).2 inferInstance
          mono_f := ⟨fun _ _ _ ↦ (hzi _).eq_of_tgt _ _⟩
          epi_g := by
            change Epi (((i)^*[A]).map (b.unit.app F))
            infer_instance }
    · have hu : IsIso a.unit := a.unit_isIso_of_L_fully_faithful
      have hfj : IsIso (((j)^*[A]).map (a.counit.app F)) := by
        have h := a.right_triangle_components (Y := F)
        rw [← IsIso.inv_eq_of_hom_inv_id h]
        infer_instance
      have : IsIso ((Q.map ((j)^*[A])).f) := hfj
      have hgj : (Q.map ((j)^*[A])).g = 0 := (hz _).eq_of_tgt _ _
      exact
        { exact := (ShortComplex.exact_iff_epi _ hgj).2 inferInstance
          mono_f := by
            change Mono (((j)^*[A]).map (a.counit.app F))
            infer_instance
          epi_g := ⟨fun _ _ _ ↦ (hz _).eq_of_src _ _⟩ }
  exact ⟨hQ.mono_f, hQ.epi_g, hQ.exact.exact_toComposableArrows⟩

end AlgebraicGeometry.ProEtale
