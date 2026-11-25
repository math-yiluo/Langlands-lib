/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

/-! # Filtered colimits commute with cochain homology

Source: Stacks Project, Tag 0954, proof of Lemma 47.8.2.
-/

@[expose] public section

universe u v
open CategoryTheory Limits

namespace ModuleCat

/-- Filtered colimits of module complexes commute with homology.
Source: Stacks Project, Tag 0954, proof of Lemma 47.8.2, passage of the
filtered colimit through cohomology.
(blueprint: lem-sbc-filtered-colimit-cochain-homology).

Proof: Colimits of module complexes are computed in every degree. Filtered
colimits of modules are exact: a finite equation holds in a filtered colimit
if it holds at some later stage. Consequently they preserve kernels, images
and cokernels. Apply this first to the kernels of the outgoing differentials,
then to the images of the incoming differentials, and finally to the quotient
of cycles by boundaries. This yields the displayed isomorphism between the
colimit of the homology modules and the homology of the colimit complex.
In degree zero there is no incoming differential and the same argument uses
the zero boundary module. The argument applies to arbitrary modules and
small filtered categories, with no Noetherian or finite-generation assumption. -/
theorem nonempty_colimit_homology_iso
    {R : Type (max u v)} [CommRing R] {D : Type v} [SmallCategory D] [IsFiltered D]
    (F : D ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ) (q : ℕ) :
    Nonempty (colimit (F ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℕ) q) ≅
      (colimit F).homology q) := by
  have : AB5OfSize.{v, v} (ModuleCat.{max u v} R) :=
    AB5OfSize_of_univLE.{v, v, max u v, max u v} _
  let S := (ShortComplex.functorEquivalence D (ModuleCat.{max u v} R)).inverse.obj
    (F ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v} R)
      (ComplexShape.up ℕ) q)
  let e : (F ⋙ HomologicalComplex.homologyFunctor
      (ModuleCat.{max u v} R) (ComplexShape.up ℕ) q) ≅ S.homology :=
    NatIso.ofComponents (fun d ↦ S.mapHomologyIso ((evaluation D _).obj d)) (by
      intro i j f
      change ShortComplex.homologyMap (S.mapNatTrans ((evaluation D _).map f)) ≫ _ = _
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp)
  let c := HomologicalComplex.coconeOfHasColimitEval F
  let z := (colimit.isColimit F).coconePointUniqueUpToIso
    (HomologicalComplex.isColimitCoconeOfHasColimitEval F)
  let t : S.map (colim (J := D) (C := ModuleCat.{max u v} R)) ≅ c.pt.sc q :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl) (by simp; rfl)
  exact ⟨HasColimit.isoOfNatIso e ≪≫
    (S.mapHomologyIso (colim (J := D) (C := ModuleCat.{max u v} R))).symm ≪≫
      ShortComplex.homologyMapIso t ≪≫
        (HomologicalComplex.homologyFunctor _ _ q).mapIso z.symm⟩

end ModuleCat
