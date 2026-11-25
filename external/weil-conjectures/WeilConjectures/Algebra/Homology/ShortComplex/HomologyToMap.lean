/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The comparison map `H(F S) ⟶ F(H S)` for a left exact functor

Let `F : C ⥤ D` be an additive left exact functor between abelian categories and
`S : ShortComplex C`. Since `F` preserves kernels, the cycles of `S.map F` identify with
`F.obj S.cycles` (`ShortComplex.mapCyclesIsoOfLeftExact`). Composing with
`F.map S.homologyπ` gives a canonical morphism
`ShortComplex.homologyToMap F S : (S.map F).homology ⟶ F.obj S.homology`,
which is natural in `S` and in `F`, compatible with composition of functors, and an isomorphism
(equal to `S.mapHomologyIso F`) when `F` is exact.

We also provide the version `HomologicalComplex.homologyToMap` for homological complexes.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]

section
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (S : ShortComplex C)

/-- For a left exact functor `F`, the canonical isomorphism `(S.map F).cycles ≅ F.obj S.cycles`
(as `F` preserves the kernel of `S.g`). -/
noncomputable def mapCyclesIsoOfLeftExact : (S.map F).cycles ≅ F.obj S.cycles :=
  ((S.map F).isoCyclesOfIsLimit (isLimitForkMapOfIsLimit' F S.iCycles_g
    S.cyclesIsKernel)).symm

@[reassoc (attr := simp)]
lemma mapCyclesIsoOfLeftExact_hom_iCycles :
    (mapCyclesIsoOfLeftExact F S).hom ≫ F.map S.iCycles = (S.map F).iCycles :=
  (S.map F).isoCyclesOfIsLimit_inv_ι
    (isLimitForkMapOfIsLimit' F S.iCycles_g S.cyclesIsKernel)

@[reassoc (attr := simp)]
lemma mapCyclesIsoOfLeftExact_inv_iCycles :
    (mapCyclesIsoOfLeftExact F S).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  rw [← mapCyclesIsoOfLeftExact_hom_iCycles, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma toCycles_mapCyclesIsoOfLeftExact_hom :
    (S.map F).toCycles ≫ (mapCyclesIsoOfLeftExact F S).hom = F.map S.toCycles := by
  rw [← cancel_mono (F.map S.iCycles), Category.assoc, mapCyclesIsoOfLeftExact_hom_iCycles,
    ← F.map_comp, toCycles_i, toCycles_i, map_f]

/-- For a left exact functor `F`, the canonical comparison morphism
`(S.map F).homology ⟶ F.obj S.homology`. -/
noncomputable def homologyToMap : (S.map F).homology ⟶ F.obj S.homology :=
  (S.map F).descHomology ((mapCyclesIsoOfLeftExact F S).hom ≫ F.map S.homologyπ) (by
    rw [toCycles_mapCyclesIsoOfLeftExact_hom_assoc, ← F.map_comp, toCycles_comp_homologyπ,
      F.map_zero])

@[reassoc (attr := simp)]
lemma π_homologyToMap :
    (S.map F).homologyπ ≫ homologyToMap F S =
      (mapCyclesIsoOfLeftExact F S).hom ≫ F.map S.homologyπ :=
  π_descHomology _ _ _

/-- Naturality of `mapCyclesIsoOfLeftExact` in the short complex. -/
@[reassoc]
lemma cyclesMap_mapCyclesIsoOfLeftExact_hom {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    cyclesMap (F.mapShortComplex.map φ) ≫ (mapCyclesIsoOfLeftExact F S₂).hom =
      (mapCyclesIsoOfLeftExact F S₁).hom ≫ F.map (cyclesMap φ) := by
  rw [← cancel_mono (F.map S₂.iCycles), Category.assoc, Category.assoc,
    mapCyclesIsoOfLeftExact_hom_iCycles, ← F.map_comp, cyclesMap_i, F.map_comp,
    mapCyclesIsoOfLeftExact_hom_iCycles_assoc]
  exact cyclesMap_i (F.mapShortComplex.map φ)

/-- Naturality of `homologyToMap` in the short complex. -/
@[reassoc]
lemma homologyMap_homologyToMap {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    homologyMap (F.mapShortComplex.map φ) ≫ homologyToMap F S₂ =
      homologyToMap F S₁ ≫ F.map (homologyMap φ) := by
  rw [← cancel_epi (S₁.map F).homologyπ, π_homologyToMap_assoc, ← F.map_comp,
    homologyπ_naturality, F.map_comp, ← cyclesMap_mapCyclesIsoOfLeftExact_hom_assoc,
    ← π_homologyToMap]
  exact homologyπ_naturality_assoc (F.mapShortComplex.map φ) _

end

section

variable {F F' : C ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  [F'.Additive] [PreservesFiniteLimits F'] (α : F ⟶ F') (S : ShortComplex C)

/-- Naturality of `mapCyclesIsoOfLeftExact` in the functor. -/
@[reassoc]
lemma cyclesMap_mapNatTrans_mapCyclesIsoOfLeftExact_hom :
    cyclesMap (S.mapNatTrans α) ≫ (mapCyclesIsoOfLeftExact F' S).hom =
      (mapCyclesIsoOfLeftExact F S).hom ≫ α.app S.cycles := by
  rw [← cancel_mono (F'.map S.iCycles), Category.assoc, Category.assoc,
    mapCyclesIsoOfLeftExact_hom_iCycles, cyclesMap_i, ← α.naturality,
    mapCyclesIsoOfLeftExact_hom_iCycles_assoc]
  rfl

/-- Naturality of `homologyToMap` in the functor. -/
@[reassoc]
lemma homologyMap_mapNatTrans_homologyToMap :
    homologyMap (S.mapNatTrans α) ≫ homologyToMap F' S =
      homologyToMap F S ≫ α.app S.homology := by
  rw [← cancel_epi (S.map F).homologyπ, homologyπ_naturality_assoc, π_homologyToMap,
    cyclesMap_mapNatTrans_mapCyclesIsoOfLeftExact_hom_assoc, π_homologyToMap_assoc,
    α.naturality]

end

section

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteLimits (F ⋙ G)]
  (S : ShortComplex C)

lemma mapCyclesIsoOfLeftExact_comp :
    mapCyclesIsoOfLeftExact (F ⋙ G) S =
      mapCyclesIsoOfLeftExact G (S.map F) ≪≫ G.mapIso (mapCyclesIsoOfLeftExact F S) := by
  ext
  rw [← cancel_mono ((F ⋙ G).map S.iCycles)]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Functor.comp_map,
    ← G.map_comp, mapCyclesIsoOfLeftExact_hom_iCycles]
  exact mapCyclesIsoOfLeftExact_hom_iCycles (F ⋙ G) S

/-- Compatibility of `homologyToMap` with the composition of functors
(note that `S.map (F ⋙ G) = (S.map F).map G` holds definitionally). -/
lemma homologyToMap_comp :
    homologyToMap (F ⋙ G) S = homologyToMap G (S.map F) ≫ G.map (homologyToMap F S) := by
  refine (cancel_epi ((S.map F).map G).homologyπ).1 ?_
  rw [π_homologyToMap_assoc]
  refine (π_homologyToMap (F ⋙ G) S).trans ?_
  rw [mapCyclesIsoOfLeftExact_comp, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    Functor.comp_map, ← G.map_comp, ← G.map_comp, π_homologyToMap]

end

section

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [F.PreservesHomology]
  (S : ShortComplex C)

lemma mapCyclesIsoOfLeftExact_eq_mapCyclesIso :
    mapCyclesIsoOfLeftExact F S = S.mapCyclesIso F := by
  ext
  rw [← cancel_mono (F.map S.iCycles), mapCyclesIsoOfLeftExact_hom_iCycles,
    mapCyclesIso_hom_iCycles]

/-- When `F` is exact, `homologyToMap F S` is the canonical isomorphism `S.mapHomologyIso F`. -/
lemma homologyToMap_eq_mapHomologyIso_hom :
    homologyToMap F S = (S.mapHomologyIso F).hom := by
  rw [← cancel_epi (S.map F).homologyπ, π_homologyToMap,
    S.leftHomologyData.mapHomologyIso_eq F, mapCyclesIsoOfLeftExact_eq_mapCyclesIso,
    S.leftHomologyData.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc, LeftHomologyData.map_π,
    ← F.map_comp, LeftHomologyData.π_comp_homologyIso_inv]

instance isIso_homologyToMap : IsIso (homologyToMap F S) := by
  rw [homologyToMap_eq_mapHomologyIso_hom]
  infer_instance

end

end CategoryTheory.ShortComplex

namespace HomologicalComplex

open CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
  {ι : Type*} {c : ComplexShape ι}

/-- For a left exact functor `F`, the canonical comparison morphism
`H_i(F K) ⟶ F(H_i K)`. -/
noncomputable abbrev homologyToMap (K : HomologicalComplex C c) (i : ι) :
    ((F.mapHomologicalComplex c).obj K).homology i ⟶ F.obj (K.homology i) :=
  ShortComplex.homologyToMap F (K.sc i)

/-- Naturality of `HomologicalComplex.homologyToMap` in chain maps. -/
@[reassoc]
lemma homologyMap_homologyToMap {K L : HomologicalComplex C c} (f : K ⟶ L) (i : ι) :
    homologyMap ((F.mapHomologicalComplex c).map f) i ≫ homologyToMap F L i =
      homologyToMap F K i ≫ F.map (homologyMap f i) :=
  ShortComplex.homologyMap_homologyToMap F ((shortComplexFunctor C c i).map f)

instance isIso_homologyToMap [F.PreservesHomology] (K : HomologicalComplex C c) (i : ι) :
    IsIso (homologyToMap F K i) :=
  ShortComplex.isIso_homologyToMap F (K.sc i)

/-- Naturality of `HomologicalComplex.homologyToMap` in the functor. -/
@[reassoc]
lemma homologyMap_mapHomologicalComplex_app_homologyToMap {F F' : C ⥤ D} [F.Additive]
    [Limits.PreservesFiniteLimits F] [F'.Additive] [Limits.PreservesFiniteLimits F']
    (α : F ⟶ F') (K : HomologicalComplex C c) (i : ι) :
    homologyMap ((NatTrans.mapHomologicalComplex α c).app K) i ≫ homologyToMap F' K i =
      homologyToMap F K i ≫ α.app (K.homology i) :=
  ShortComplex.homologyMap_mapNatTrans_homologyToMap α (K.sc i)

/-- Compatibility of `HomologicalComplex.homologyToMap` with the composition of functors. -/
lemma homologyToMap_comp {E : Type*} [Category* E] [Abelian E] (G : D ⥤ E) [G.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteLimits (F ⋙ G)]
    (K : HomologicalComplex C c) (i : ι) :
    homologyToMap (F ⋙ G) K i =
      homologyToMap G ((F.mapHomologicalComplex c).obj K) i ≫ G.map (homologyToMap F K i) :=
  ShortComplex.homologyToMap_comp F G (K.sc i)

end HomologicalComplex
