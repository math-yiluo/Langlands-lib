/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Homology of the bounded below right derived functor on acyclic complexes

Let `F : C ⥤ D` be a left exact additive functor between abelian categories, where `C` has
enough injectives. We compute the homology of `F.rightDerivedFunctorPlus` on bounded below
complexes of `F`-acyclic objects.

## Main results

- `CategoryTheory.Functor.nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso`: if `L` is a
  bounded below complex of `F`-acyclic objects and `F` is left exact, then
  `H^n(R⁺F(L)) ≅ H^n(F(L))`.
- `CategoryTheory.Functor.nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso_of_quasiIso`:
  more generally, if `K ⟶ L` is a quasi-isomorphism to such a complex, then
  `H^n(R⁺F(K)) ≅ H^n(F(L))`.
- `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic`: if `G` is left exact
  and `F` sends injective objects to `G`-acyclic objects, then `R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G`.
-/

@[expose] public section

namespace CategoryTheory

open Limits ZeroObject

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

namespace Functor

variable (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

section

variable [HasDerivedCategory C] [HasDerivedCategory D]

/-- **Acyclic complexes compute `R⁺F`.** If `F` is left exact and `L` is a bounded below
complex of `F`-acyclic objects, then the homology of `R⁺F(L)` is the homology of `F(L)`. -/
theorem nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso [PreservesFiniteLimits F]
    (L : CochainComplex.Plus C) (hL : ∀ n, F.rightAcyclic (L.obj.X n)) (n : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor D n).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L)) ≅
      ((F.mapHomologicalComplex _).obj L.obj).homology n) := by
  obtain ⟨a, ha⟩ := L.2
  obtain ⟨T, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective L a
  let T' := (InjectiveObject.ι C).mapCochainComplexPlus.obj T
  have : QuasiIso i.hom := hi
  have : ∀ n, Injective (T'.obj.X n) := fun n ↦ (T.obj.X n).2
  have : T'.obj.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ _ _).2 ‹_›
  have := F.quasiIso_map_of_rightAcyclic i.hom a hL
    (fun n ↦ F.rightAcyclic_of_injective _)
  have : IsIso (DerivedCategory.Plus.Q.map i) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C) i hi
  exact ⟨(DerivedCategory.Plus.homologyFunctor D n).mapIso
      (F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map i))) ≪≫
    F.homologyRightDerivedFunctorPlusObjQIsoOfInjective T' n ≪≫
    (asIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map i.hom) n)).symm⟩

/-- **Acyclic resolutions of complexes compute `R⁺F`.** If `F` is left exact and `φ : K ⟶ L`
is a quasi-isomorphism from a bounded below complex `K` to a bounded below complex `L` of
`F`-acyclic objects, then `H^n(R⁺F(K)) ≅ H^n(F(L))` for all `n`.
(blueprint: `lemma-acyclic-resolutions`, item 3) -/
theorem nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso_of_quasiIso [PreservesFiniteLimits F]
    {K L : CochainComplex.Plus C} (φ : K ⟶ L) [QuasiIso φ.hom]
    (hL : ∀ n, F.rightAcyclic (L.obj.X n)) (n : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor D n).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
      ((F.mapHomologicalComplex _).obj L.obj).homology n) := by
  have : IsIso (DerivedCategory.Plus.Q.map φ) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C) φ
      (show QuasiIso φ.hom from inferInstance)
  obtain ⟨e⟩ := F.nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso L hL n
  exact ⟨(DerivedCategory.Plus.homologyFunctor D n).mapIso
    (F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map φ))) ≪≫ e⟩


/-- **Acyclic complexes compute `R⁺F`, at the level of the unit.** If `F` is left exact and `L`
is a bounded below complex of `F`-acyclic objects, then the unit `F(L) ⟶ R⁺F(L)` is an
isomorphism in `DerivedCategory.Plus D`. Choose a quasi-isomorphism `i : L ⟶ T` to a bounded
below complex of injectives. In the naturality square of the unit
```
F(L) ----unit----> R⁺F(L)
 |                   |
F(i)              R⁺F(i)
 v                   v
F(T) ----unit----> R⁺F(T)
```
the bottom map is an isomorphism as `T` is injective, `R⁺F(i)` is an isomorphism as `i` is a
quasi-isomorphism, and `F(i)` is an isomorphism by `Functor.quasiIso_map_of_rightAcyclic`. -/
theorem isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic [PreservesFiniteLimits F]
    (L : CochainComplex.Plus C) (hL : ∀ n, F.rightAcyclic (L.obj.X n)) :
    IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj L)) := by
  obtain ⟨a, ha⟩ := L.2
  obtain ⟨T, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective L a
  let T' := (InjectiveObject.ι C).mapCochainComplexPlus.obj T
  have : QuasiIso i.hom := hi
  have : ∀ n, Injective (T'.obj.X n) := fun n ↦ (T.obj.X n).2
  have : T'.obj.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ _ _).2 ‹_›
  have hFi := F.quasiIso_map_of_rightAcyclic i.hom a hL
    (fun n ↦ F.rightAcyclic_of_injective _)
  have h₁ : IsIso (DerivedCategory.Plus.Qh.map
      (F.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient C).map i))) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hFi)
  have h₂ : IsIso (F.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i))) := by
    have : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i)) :=
      Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hi)
    infer_instance
  have h₃ : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient C).obj T')) := inferInstance
  have hnat := F.rightDerivedFunctorPlusUnith.naturality ((HomotopyCategory.Plus.quotient C).map i)
  dsimp only [Functor.comp_map] at hnat
  have : IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj L) ≫
      F.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i))) := by
    rw [← hnat]; infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlus.map
    (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i)))

end

section Composition

variable {E : Type*} [Category* E] [Abelian E] [EnoughInjectives D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G]

/-- If `G` is left exact and `F` sends injective objects to `G`-acyclic objects, then
`R⁺F ⋙ R⁺G`, with the composite unit, is a right derived functor of `F ⋙ G`: on a bounded below
complex `K` of injectives the unit of `R⁺F` is an isomorphism, and so is the unit of `R⁺G` at
the complex `F(K)` of `G`-acyclic objects
(`Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`). -/
lemma isRightDerivedFunctor_rightDerivedFunctorPlus_comp_of_rightAcyclic
    (hFG : ∀ (I : C) [Injective I], G.rightAcyclic (F.obj I)) :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightDerivedFunctorPlusCompUnit F G) (HomotopyCategory.Plus.quasiIso C) := by
  refine (HomotopyCategory.Plus.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  set K : HomotopyCategory.Plus C := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X₁
  have h₁ : IsIso (F.rightDerivedFunctorPlusUnith.app K) := inferInstance
  let L : CochainComplex.Plus D := ⟨(F.mapHomotopyCategoryPlus.obj K).obj.as,
    (HomotopyCategory.plus_quotient_obj_iff _).1 (F.mapHomotopyCategoryPlus.obj K).property⟩
  have h₂ : IsIso (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)) :=
    G.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic L (fun n ↦
      have : Injective (K.obj.as.X n) := inferInstanceAs (Injective ((X₁.obj.as.X n).obj))
      hFG (K.obj.as.X n))
  rw [rightDerivedFunctorPlusCompUnit_app]
  infer_instance

/-- **Composition of bounded below right derived functors with acyclicity.** If `G` is left
exact and `F` sends injective objects to `G`-acyclic objects, then the canonical comparison
`R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G` is an isomorphism. -/
noncomputable def rightDerivedFunctorPlusCompIsoOfRightAcyclic
    (hFG : ∀ (I : C) [Injective I], G.rightAcyclic (F.obj I)) :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  have := F.isRightDerivedFunctor_rightDerivedFunctorPlus_comp_of_rightAcyclic G hFG
  rightDerivedUnique (F ⋙ G).rightDerivedFunctorPlus
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (F ⋙ G).rightDerivedFunctorPlusUnith (rightDerivedFunctorPlusCompUnit F G)
    (HomotopyCategory.Plus.quasiIso C)

end Composition

end Functor

end CategoryTheory
