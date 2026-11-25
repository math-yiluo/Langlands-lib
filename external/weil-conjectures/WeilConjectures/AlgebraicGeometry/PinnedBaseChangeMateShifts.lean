/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts
import WeilConjectures.AlgebraicGeometry.PinnedDerivedAdjunctionShifts

/-! # Shift compatibility of the canonical derived base-change mate
Source: Stacks Project, Tag 08HY.
(blueprint: lem-pc-pinned-base-change-mate-shifts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

private theorem pullback_eqToHom_commShift
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (s : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (derivedPullback.{u, w} f).CommShift ℤ)
    {X Y : Scheme.{u}} {k l : X ⟶ Y} (h : k = l) :
    letI := s k
    letI := s l
    NatTrans.CommShift (eqToHom (congrArg (fun f ↦ derivedPullback.{u, w} f) h)) ℤ := by
  subst l
  simp only [eqToHom_refl]
  infer_instance

/-- The base-change components form a natural transformation commuting with shift,
when pullback shifts are transported using the selected left-derived counits.
Source: Stacks Project, Tag 08HY, canonical base-change mate.
(blueprint: lem-pc-pinned-base-change-mate-shifts).
Proof: the Hom equivalences of the selected derived adjunctions are pinned to the
underived adjunction and the selected left-derived counits, as recorded in
exists_schemeDerivedAdjunction. Hence their units and counits commute with the
shift comparisons transported through these counits and the right-derived units.
The composition comparison is the unique left-derived lift of termwise tensor
reassociation, which commutes with shift. Its inverse does too. Equality
transport along the square is compatible with these comparisons. Naturality of
all these maps and of the adjunction Hom equivalence first constructs the stated
natural transformation. The shift equations for the composition comparison,
adjunction counit and transpose then prove NatTrans.CommShift for this
transformation. This is a statement about arbitrary derived objects, before
restriction to singles and before the final tensor counit or H. -/
theorem exists_pinned_base_change_mate_shifts
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    (s : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (derivedPullback.{u, w} f).CommShift ℤ)
    (hs : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      letI := s f
      NatTrans.CommShift (pinnedPullbackCounit.{u, w} f) ℤ)
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g) :
    letI := s g
    letI := s g'
    ∃ τ : schemeDerivedDirectImage.{u, w, w} f ⋙ derivedPullback.{u, w} g ⟶
        derivedPullback.{u, w} g' ⋙ schemeDerivedDirectImage.{u, w, w} f',
      (∀ E, τ.app E = schemeDerivedBaseChangeMap.{u, w} f f' g g' h E) ∧
        NatTrans.CommShift τ ℤ := by
  classical
  let _ := s f
  let _ := s f'
  let _ := s g
  let _ := s g'
  let _ := s (f' ≫ g)
  let _ := s (g' ≫ f)
  have := pinnedPullbackComposition_commShift s hs f' g
  have := pinnedPullbackComposition_commShift s hs g' f
  have := pinnedDerivedAdjunction_commShift s hs f
  have := pinnedDerivedAdjunction_commShift s hs f'
  have htransport : NatTrans.CommShift
      (eqToHom (congrArg (fun k ↦ derivedPullback.{u, w} k) h.symm)) ℤ :=
    pullback_eqToHom_commShift s h.symm
  let γ : (schemeDerivedDirectImage f ⋙ derivedPullback g) ⋙ derivedPullback f' ⟶
      derivedPullback g' :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (pinnedPullbackComposition f' g).hom ≫
      Functor.whiskerLeft _ (eqToHom (congrArg (fun k ↦ derivedPullback k) h.symm)) ≫
      Functor.whiskerLeft _ (pinnedPullbackComposition g' f).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (pinnedDerivedAdjunction f).counit (derivedPullback g') ≫
      (Functor.leftUnitor _).hom
  have : NatTrans.CommShift γ ℤ := by dsimp only [γ]; infer_instance
  let τ : schemeDerivedDirectImage f ⋙ derivedPullback g ⟶
      derivedPullback g' ⋙ schemeDerivedDirectImage f' :=
    (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft _ (pinnedDerivedAdjunction f').unit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight γ (schemeDerivedDirectImage f')
  refine ⟨τ, ?_, ?_⟩
  · intro E
    dsimp only [τ, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app]
    simp only [Category.id_comp]
    change (pinnedDerivedAdjunction f').unit.app _ ≫
      (schemeDerivedDirectImage f').map (γ.app E) = _
    change (pinnedDerivedAdjunction f').homEquiv _ _ (γ.app E) = _
    congr 1
    simp only [γ, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, eqToHom_app, Category.id_comp]
    change _ ≫ _ ≫ _ ≫ _ ≫ 𝟙 _ = _
    simp only [Category.comp_id]
  · dsimp only [τ]
    infer_instance

end AlgebraicGeometry
