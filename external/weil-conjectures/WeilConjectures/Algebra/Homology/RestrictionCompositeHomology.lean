/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso

/-! # Composition of restriction homology comparisons -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ModuleCat

private theorem homologyIso_comp
    {C E B : Type*} [Category C] [Category E] [Category B]
    [Abelian C] [Abelian E] [Abelian B]
    (S : ShortComplex C) (F : C ⥤ E) (G : E ⥤ B)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [(F ⋙ G).PreservesHomology] :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  let h := S.homologyData.left
  have hc : ((h.map F).map G).cyclesIso.hom = (h.map (F ⋙ G)).cyclesIso.hom := by
    apply (cancel_mono ((F ⋙ G).map h.i)).1
    change ((h.map F).map G).cyclesIso.hom ≫ ((h.map F).map G).i =
      (h.map (F ⋙ G)).cyclesIso.hom ≫ (h.map (F ⋙ G)).i
    rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
      ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
    rfl
  have hh : ((h.map F).map G).homologyIso.hom = (h.map (F ⋙ G)).homologyIso.hom := by
    apply (cancel_epi ((S.map (F ⋙ G)).homologyπ)).1
    rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, hc]
    rfl
  rw [h.mapHomologyIso_eq (F ⋙ G), (h.map F).mapHomologyIso_eq G,
    h.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp]
  simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id_assoc]
  rw [hh]
  rfl

/-- Restriction to two successive coefficient rings commutes with homology.
Source: Stacks Project, Tag 06Y6; the exactness of restriction of scalars.
(blueprint: lem-pc-restriction-composite-homology).

Proof: all three maps are the canonical maps induced on kernel modulo image by
restriction of scalars. Compose their defining equations with the quotient map
from cycles; naturality of the kernel comparison gives identical maps. Cancel
the quotient epimorphism to obtain the equality. Restriction changes only the
scalar action, and so preserves both kernels and cokernels, including over zero
rings and for complexes with zero homology. -/
theorem restrictionCompositeHomology
    (D E B : Type u) [CommRing D] [CommRing E] [CommRing B]
    (f : E →+* D) (g : B →+* E) (P : CochainComplex (ModuleCat.{u} D) ℤ) (i : ℤ) :
    ((restrictScalars.{u} f ⋙ restrictScalars.{u} g).mapHomologicalComplexHomologyIso
      (.up ℤ) i).hom.app P =
    (((((restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).obj P).sc i).mapHomologyIso
       (restrictScalars.{u} g)).hom ≫
    (restrictScalars.{u} g).map (((P.sc i).mapHomologyIso (restrictScalars.{u} f)).hom) := by
  with_unfolding_all simpa [Functor.mapHomologicalComplexHomologyIso,
    Functor.mapHomologicalComplexCompShortComplexFunctorIso,
    ShortComplex.homologyFunctorIso, HomologicalComplex.homologyFunctorIso,
    HomologicalComplex.homology, HomologicalComplex.homologyFunctor,
    HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor', Functor.mapHomologicalComplex,
    ShortComplex.map]
    using homologyIso_comp (P.sc i) (restrictScalars.{u} f) (restrictScalars.{u} g)

end ModuleCat
