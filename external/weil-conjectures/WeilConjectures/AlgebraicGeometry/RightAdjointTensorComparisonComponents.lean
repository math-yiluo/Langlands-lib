/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
/-- The pinned projection family has a natural right-adjoint mate.
Source: Stacks Project, Tag 0A9U; naturality of the monoidal comparison,
counits, and adjunction hom equivalences.
Proof: expand the displayed component and use naturality of the monoidal
comparison, both counits, the right unitor, and adjunction hom equivalence.
(blueprint: lem-sc-right-adjoint-tensor-comparison-components) -/
theorem rightAdjointTensorComparison_components
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
    (pf : ∀ K : schemeDerivedQCohCategory Y,
      (schemeDerivedDirectImage f).obj
          (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
        K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)
    (hpf : ∀ K, (pf K).inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj)) :
    let F := (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
    ∃ τ : F ⟶ c, ∀ K,
      τ.app K = ((adj.homEquiv
          ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
            hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
          (ObjectProperty.homMk ((pf K).hom ≫
            K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom))) := by
  dsimp only
  let E := (c.obj ⟨𝟙_ _, hO⟩).obj
  -- Transpose the pinned inverses to use oplax naturality and tensor interchange.
  have hinv (K L : schemeDerivedQCohCategory Y) (g : K ⟶ L) :
      g.hom ▷ (schemeDerivedDirectImage f).obj E ≫ (pf L).inv =
        (pf K).inv ≫ (schemeDerivedDirectImage f).map
          ((derivedPullback f).map g.hom ▷ E) := by
    rw [hpf K, hpf L, ← a.homEquiv_naturality_left,
      ← a.homEquiv_naturality_right]
    congr 1
    simp only [Functor.Monoidal.μIso_inv]
    rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural_left]
    simp only [Category.assoc]
    rw [← whisker_exchange]
    rfl
  -- Naturality of the inverse family gives naturality of the forward family.
  have hhom (K L : schemeDerivedQCohCategory Y) (g : K ⟶ L) :
      (schemeDerivedDirectImage f).map ((derivedPullback f).map g.hom ▷ E) ≫
          (pf L).hom = (pf K).hom ≫ g.hom ▷ (schemeDerivedDirectImage f).obj E := by
    rw [← cancel_epi (pf K).inv]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, ← hinv K L g]
    simp
  -- The component formula is natural after transposition along the right adjunction.
  refine ⟨?_, ?_⟩
  · refine
      { app := fun K ↦ by
          exact (adj.homEquiv
            ⟨((derivedPullback f).obj K.obj) ⊗ E, hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk ((pf K).hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom))
        naturality := ?_ }
    intro K L g
    apply adj.homEquiv_naturality_left_square
    ext
    change (schemeDerivedDirectImage f).map ((derivedPullback f).map g.hom ▷ E) ≫
        ((pf L).hom ≫ L.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ L.obj).hom) =
      ((pf K).hom ≫ K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom) ≫ g.hom
    rw [← Category.assoc, hhom K L g]
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc]
    dsimp only [Functor.id_obj]
    rw [rightUnitor_naturality]
  · intro K
    rfl
end AlgebraicGeometry
