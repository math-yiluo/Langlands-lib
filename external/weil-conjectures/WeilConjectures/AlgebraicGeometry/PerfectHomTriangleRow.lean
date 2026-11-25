/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ExactSequence
public import WeilConjectures.AlgebraicGeometry.DerivedCategory

/-! # Five-term additive Hom rows and their triangle presentations

Source: Stacks Project, Tags 0149 and 08BW.
(blueprint: lem-pc-perfect-hom-triangle-row-presentations).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
namespace AlgebraicGeometry

/-- The five terms from Hom(M,T₂[-1]) through Hom(M,T₃), with the canonical
connecting map. This is a construction from the supplied triangle, without choices.
Source: Stacks Project, Tags 0149 and 08BW.
(blueprint: lem-pc-perfect-hom-triangle-row-presentations). -/
noncomputable def perfectHomTriangleRow (Z : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (M : schemeDerivedCategory Z) (T : Triangle (schemeDerivedCategory Z)) :
    ComposableArrows AddCommGrpCat.{max u w} 4 :=
  let F := preadditiveCoyoneda.obj (Opposite.op M)
  ComposableArrows.mk₄
    (AddCommGrpCat.uliftFunctor.{u}.map ((F.shift (-1 : ℤ)).map T.mor₂))
    (AddCommGrpCat.uliftFunctor.{u}.map (F.homologySequenceδ T (-1) 0 (by decide)))
    (AddCommGrpCat.uliftFunctor.{u}.map ((F.shift (0 : ℤ)).map T.mor₁))
    (AddCommGrpCat.uliftFunctor.{u}.map ((F.shift (0 : ℤ)).map T.mor₂))

/-- Additive Hom rows are functorial in the supplied triangle. The boundary square
is the naturality square of the canonical homology-sequence boundary.
Source: Stacks Project, Tags 0149 and 08BW.
(blueprint: lem-pc-perfect-hom-triangle-row-presentations). -/
noncomputable def perfectHomTriangleRowFunctor (Z : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (M : schemeDerivedCategory Z) :
    Triangle (schemeDerivedCategory Z) ⥤ ComposableArrows AddCommGrpCat.{max u w} 4 := by
  let F := preadditiveCoyoneda.obj (Opposite.op M)
  let L := AddCommGrpCat.uliftFunctor.{u}
  refine
    { obj := perfectHomTriangleRow Z M
      map := fun {T T'} φ ↦ ComposableArrows.homMk₄
        (L.map ((F.shift (-1 : ℤ)).map φ.hom₂))
        (L.map ((F.shift (-1 : ℤ)).map φ.hom₃))
        (L.map ((F.shift (0 : ℤ)).map φ.hom₁))
        (L.map ((F.shift (0 : ℤ)).map φ.hom₂))
        (L.map ((F.shift (0 : ℤ)).map φ.hom₃)) ?_ ?_ ?_ ?_
      map_id := ?_
      map_comp := ?_ }
  · change L.map _ ≫ L.map _ = L.map _ ≫ L.map _
    rw [← L.map_comp, ← L.map_comp, ← Functor.map_comp, ← Functor.map_comp, φ.comm₂]
  · change L.map _ ≫ L.map _ = L.map _ ≫ L.map _
    rw [← L.map_comp, ← L.map_comp]
    exact congrArg L.map (F.homologySequenceδ_naturality φ (-1) 0 (by decide)).symm
  · change L.map _ ≫ L.map _ = L.map _ ≫ L.map _
    rw [← L.map_comp, ← L.map_comp, ← Functor.map_comp, ← Functor.map_comp, φ.comm₁]
  · change L.map _ ≫ L.map _ = L.map _ ≫ L.map _
    rw [← L.map_comp, ← L.map_comp, ← Functor.map_comp, ← Functor.map_comp, φ.comm₂]
  · intro T
    apply ComposableArrows.hom_ext₄
    · change L.map ((F.shift (-1 : ℤ)).map (𝟙 T.obj₂)) = 𝟙 _
      exact (F.shift (-1 : ℤ) ⋙ L).map_id T.obj₂
    · change L.map ((F.shift (-1 : ℤ)).map (𝟙 T.obj₃)) = 𝟙 _
      exact (F.shift (-1 : ℤ) ⋙ L).map_id T.obj₃
    · change L.map ((F.shift (0 : ℤ)).map (𝟙 T.obj₁)) = 𝟙 _
      exact (F.shift (0 : ℤ) ⋙ L).map_id T.obj₁
    · change L.map ((F.shift (0 : ℤ)).map (𝟙 T.obj₂)) = 𝟙 _
      exact (F.shift (0 : ℤ) ⋙ L).map_id T.obj₂
    · change L.map ((F.shift (0 : ℤ)).map (𝟙 T.obj₃)) = 𝟙 _
      exact (F.shift (0 : ℤ) ⋙ L).map_id T.obj₃
  · intro T T' T'' φ ψ
    apply ComposableArrows.hom_ext₄
    · change L.map ((F.shift (-1 : ℤ)).map (φ.hom₂ ≫ ψ.hom₂)) =
        L.map ((F.shift (-1 : ℤ)).map φ.hom₂) ≫
          L.map ((F.shift (-1 : ℤ)).map ψ.hom₂)
      simp only [Functor.map_comp]
    · change L.map ((F.shift (-1 : ℤ)).map (φ.hom₃ ≫ ψ.hom₃)) =
        L.map ((F.shift (-1 : ℤ)).map φ.hom₃) ≫
          L.map ((F.shift (-1 : ℤ)).map ψ.hom₃)
      simp only [Functor.map_comp]
    · change L.map ((F.shift (0 : ℤ)).map (φ.hom₁ ≫ ψ.hom₁)) =
        L.map ((F.shift (0 : ℤ)).map φ.hom₁) ≫
          L.map ((F.shift (0 : ℤ)).map ψ.hom₁)
      simp only [Functor.map_comp]
    · change L.map ((F.shift (0 : ℤ)).map (φ.hom₂ ≫ ψ.hom₂)) =
        L.map ((F.shift (0 : ℤ)).map φ.hom₂) ≫
          L.map ((F.shift (0 : ℤ)).map ψ.hom₂)
      simp only [Functor.map_comp]
    · change L.map ((F.shift (0 : ℤ)).map (φ.hom₃ ≫ ψ.hom₃)) =
        L.map ((F.shift (0 : ℤ)).map φ.hom₃) ≫
          L.map ((F.shift (0 : ℤ)).map ψ.hom₃)
      simp only [Functor.map_comp]

/-- A cocone of triangles gives a morphism from the diagram of Hom rows to its
constant limit row. This uses only whiskering and exchange of the two indices.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-triangle-row-presentations). -/
noncomputable def perfectHomTriangleRowCoconeMap (Z : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (M : schemeDerivedCategory Z) {J : Type*} [Category J]
    (T : J ⥤ Triangle (schemeDerivedCategory Z)) (c : Cocone T) :
    (T ⋙ perfectHomTriangleRowFunctor Z M).flip ⟶
      perfectHomTriangleRow Z M c.pt ⋙ Functor.const J :=
  (flipFunctor _ _ _).map
    (Functor.whiskerRight c.ι (perfectHomTriangleRowFunctor Z M) ≫
      (Functor.constComp J c.pt (perfectHomTriangleRowFunctor Z M)).hom)

section
attribute [local simp] smul_smul
variable {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (F : C ⥤ AddCommGrpCat) [F.IsHomological] [F.ShiftSequence ℤ]
  (T : Triangle C) (hT : T ∈ distTriang C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def ordinaryWindowIso (n : ℤ) :
    (ShortComplex.mk _ _ (F.homologySequence_comp T hT n)) ≅
      (shortComplexOfDistTriangle (T⟦n⟧) (T.shift_distinguished hT n)).map F :=
  (ShortComplex.isoMk ((F.isoShift n).app _)
    (n.negOnePow • ((F.isoShift n).app _)) ((F.isoShift n).app _)
    (by simp) (by simp)).symm

set_option backward.defeqAttrib.useBackward true in
private noncomputable def boundaryWindowIso :
    (ShortComplex.mk _ _ (F.comp_homologySequenceδ T hT (-1) 0 (by decide))) ≅
      (shortComplexOfDistTriangle (T.rotate⟦(-1 : ℤ)⟧)
        (T.rotate.shift_distinguished (rot_of_distTriang T hT) (-1))).map F := by
  let e : (ShortComplex.mk _ _
      (F.homologySequence_comp T.rotate (rot_of_distTriang T hT) (-1))) ≅
      (ShortComplex.mk _ _ (F.comp_homologySequenceδ T hT (-1) 0 (by decide))) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      ((F.shiftIso 1 (-1) 0 (by decide)).app _)
      (by simp) (by simp [Functor.homologySequenceδ, Functor.shiftMap])
  exact e.symm ≪≫ ordinaryWindowIso F T.rotate (rot_of_distTriang T hT) (-1)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def inverseBoundaryWindowIso :
    (ShortComplex.mk _ _ (F.homologySequenceδ_comp T hT (-1) 0 (by decide))) ≅
      (shortComplexOfDistTriangle (T.invRotate⟦(0 : ℤ)⟧)
        (T.invRotate.shift_distinguished (inv_rot_of_distTriang T hT) 0)).map F := by
  let e : (ShortComplex.mk _ _
      (F.homologySequence_comp T.invRotate (inv_rot_of_distTriang T hT) 0)) ≅
      (ShortComplex.mk _ _ (F.homologySequenceδ_comp T hT (-1) 0 (by decide))) := by
    refine ShortComplex.isoMk (-((F.shiftIso (-1) 0 (-1) (by decide)).app _))
      (Iso.refl _) (Iso.refl _) ?_ (by simp)
    dsimp
    simp only [Functor.homologySequenceδ, Preadditive.neg_comp, Functor.map_neg,
      Category.comp_id, F.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero
        T.mor₃ (-1) (neg_add_cancel 1) (-1) 0 (by decide)]
  exact e.symm ≪≫ ordinaryWindowIso F T.invRotate (inv_rot_of_distTriang T hT) 0
end

/-- Every consecutive short complex of the canonical five-term Hom row is itself
presented by additive Hom of a distinguished triangle.

Source: Stacks Project, Tags 0149 and 08BW.
(blueprint: lem-pc-perfect-hom-triangle-row-presentations).

Proof: The three zero composites are respectively the second map followed by the
boundary, the boundary followed by the first map, and the first map followed by
the second map. The distinguished-triangle identities and additivity prove them.
For the first window rotate T and shift by -1. The shift-composition comparison
identifies its third Hom term with Hom(M,T₁[0]); the sign on the middle component
removes the sign in the shifted triangle. For the second window inverse-rotate T
and shift by zero; negate the first comparison to match the inverse-rotation sign.
For the third window shift T by zero. These give short-complex isomorphisms before
ULift, which are then mapped by the additive ULift functor. Rotation, inverse
rotation, and shift preserve distinguishedness. This argument also applies to zero
objects and split triangles and uses no exactness or geometric hypotheses. -/
theorem perfectHomTriangleRow_presentations (Z : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (M : schemeDerivedCategory Z) (T : Triangle (schemeDerivedCategory Z))
    (hT : T ∈ distTriang (schemeDerivedCategory Z)) :
    ∃ h : (perfectHomTriangleRow Z M T).IsComplex,
      ∀ (r : ℕ) (hr : r + 2 ≤ 4),
        ∃ (T' : Triangle (schemeDerivedCategory Z))
          (hT' : T' ∈ distTriang (schemeDerivedCategory Z)),
          Nonempty (((perfectHomTriangleRow Z M T).sc h r hr) ≅
            (shortComplexOfDistTriangle T' hT').map
              ((preadditiveCoyoneda.obj (Opposite.op M)) ⋙
                AddCommGrpCat.uliftFunctor.{u})) := by
  let F := preadditiveCoyoneda.obj (Opposite.op M)
  let L := AddCommGrpCat.uliftFunctor.{u}
  have h : (perfectHomTriangleRow Z M T).IsComplex := by
    constructor
    intro r hr
    have cases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · change L.map _ ≫ L.map _ = 0
      rw [← L.map_comp, F.comp_homologySequenceδ T hT (-1) 0 (by decide), L.map_zero]
    · change L.map _ ≫ L.map _ = 0
      rw [← L.map_comp, F.homologySequenceδ_comp T hT (-1) 0 (by decide), L.map_zero]
    · change L.map _ ≫ L.map _ = 0
      rw [← L.map_comp, F.homologySequence_comp T hT 0, L.map_zero]
  refine ⟨h, ?_⟩
  intro r hr
  have cases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · refine ⟨T.rotate⟦(-1 : ℤ)⟧,
      T.rotate.shift_distinguished (rot_of_distTriang T hT) (-1), ?_⟩
    exact ⟨L.mapShortComplex.mapIso (boundaryWindowIso F T hT)⟩
  · refine ⟨T.invRotate⟦(0 : ℤ)⟧,
      T.invRotate.shift_distinguished (inv_rot_of_distTriang T hT) 0, ?_⟩
    exact ⟨L.mapShortComplex.mapIso (inverseBoundaryWindowIso F T hT)⟩
  · refine ⟨T⟦(0 : ℤ)⟧, T.shift_distinguished hT 0, ?_⟩
    exact ⟨L.mapShortComplex.mapIso (ordinaryWindowIso F T hT 0)⟩

end AlgebraicGeometry
