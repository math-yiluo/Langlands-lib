/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # Closure of filtered Hom continuity under extensions

The objects `K` whose shifted Hom functors `Hom(K, -[n])` carry a cocone over a filtered diagram
to a colimit (`CategoryTheory.homColimitProperty`) are closed under extensions
(`CategoryTheory.homColimitProperty_extensions`), and form a triangulated subcategory
(`CategoryTheory.isTriangulated_homColimitProperty`). -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

open scoped Pretriangulated.Opposite

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {I : Type v} [SmallCategory I] [IsFiltered I]

/-- Objects whose shifted additive Hom functors carry a specified cocone to colimits.
Source: the canonical comparison in Hemo--Richarz--Scholbach, Lemma 5.3(2).
(auxiliary; not a blueprint node) -/
def homColimitProperty (D : I ⥤ C) (c : Cocone D) : ObjectProperty C :=
  fun K ↦ ∀ n : ℤ, IsIso (colimit.desc _
    ((shiftFunctor C n ⋙ preadditiveCoyoneda.obj (op K)).mapCocone c))

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsFiltered I] in
private theorem desc_iso_transfer (D : I ⥤ C) (c : Cocone D)
    (F G : C ⥤ AddCommGrpCat.{v}) (e : F ≅ G)
    (h : IsIso (colimit.desc _ (F.mapCocone c))) :
    IsIso (colimit.desc _ (G.mapCocone c)) := by
  apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
  obtain ⟨hc⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 h
  exact ⟨IsColimit.mapCoconeEquiv e hc⟩

omit [HasZeroObject C] [Pretriangulated C] [IsFiltered I] in
private theorem homColimitProperty_shift (D : I ⥤ C) (c : Cocone D)
    (K : C) (hK : homColimitProperty D c K) (m : ℤ) :
    homColimitProperty D c (K⟦m⟧) := by
  intro n
  have : (shiftEquiv C m).functor.Additive :=
    inferInstanceAs (shiftFunctor C m).Additive
  let e : shiftFunctor C n ⋙ preadditiveCoyoneda.obj (op (K⟦m⟧)) ≅
      shiftFunctor C (n + -m) ⋙ preadditiveCoyoneda.obj (op K) :=
    Functor.isoWhiskerLeft _ ((shiftEquiv C m).toAdjunction.preadditiveCoyonedaObjIso K) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (shiftFunctorAdd C n (-m)).symm _
  exact desc_iso_transfer D c _ _ e.symm (hK (n + -m))

omit [IsFiltered I] in
private theorem exact_of_evaluations (S : ShortComplex (I ⥤ AddCommGrpCat.{v}))
    (h : ∀ i, (S.map ((evaluation I AddCommGrpCat.{v}).obj i)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).2
  apply NatTrans.ext
  funext i
  have hi : IsZero (((evaluation I AddCommGrpCat.{v}).obj i).obj S.homology) :=
    ((ShortComplex.exact_iff_isZero_homology _).1 (h i)).of_iso (S.mapHomologyIso
      ((evaluation I AddCommGrpCat.{v}).obj i)).symm
  exact hi.eq_of_src _ _

private noncomputable def colimitYoneda (D : I ⥤ C) : Cᵒᵖ ⥤ AddCommGrpCat.{v} :=
  (D ⋙ preadditiveYoneda).flip ⋙ colim

private instance diagramYoneda_additive (D : I ⥤ C) :
    (D ⋙ preadditiveYoneda).flip.Additive := ⟨by
  intro X Y f g
  apply NatTrans.ext
  funext i
  exact Functor.map_add (preadditiveYoneda.obj (D.obj i))⟩

private instance colimitYoneda_additive (D : I ⥤ C) : (colimitYoneda D).Additive := by
  dsimp [colimitYoneda]
  infer_instance

private instance colimitYoneda_homological (D : I ⥤ C) :
    (colimitYoneda D).IsHomological where
  exact T hT := by
    let S := (Pretriangulated.shortComplexOfDistTriangle T hT).map
      (D ⋙ preadditiveYoneda).flip
    have hS : S.Exact := exact_of_evaluations S (fun i ↦ by
      simpa [S, ShortComplex.map] using
        (preadditiveYoneda.obj (D.obj i)).map_distinguished_exact T hT)
    simpa [S, ShortComplex.map, colimitYoneda] using hS.map colim

private noncomputable def homColimitComparison (D : I ⥤ C) (c : Cocone D) :
    colimitYoneda D ⟶ preadditiveYoneda.obj c.pt where
  app K := colimit.desc _ ((preadditiveCoyoneda.obj K).mapCocone c)
  naturality {X Y} f := by
    dsimp [colimitYoneda]
    apply colimit.hom_ext
    intro i
    rw [ι_colimMap_assoc]
    change ((preadditiveYoneda.obj (D.obj i)).map f) ≫
        colimit.ι (D ⋙ preadditiveCoyoneda.obj Y) i ≫
          colimit.desc _ ((preadditiveCoyoneda.obj Y).mapCocone c) =
      colimit.ι (D ⋙ preadditiveCoyoneda.obj X) i ≫
        colimit.desc _ ((preadditiveCoyoneda.obj X).mapCocone c) ≫
          (preadditiveYoneda.obj c.pt).map f
    simp only [colimit.ι_desc, colimit.ι_desc_assoc]
    ext g
    exact Category.assoc _ _ _

private theorem iso_middle_of_homological
    (F G : C ⥤ AddCommGrpCat.{v}) [F.IsHomological] [G.IsHomological]
    (α : F ⟶ G) (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C)
    (h₀ : IsIso (α.app (T.obj₃⟦(-1 : ℤ)⟧)))
    (h₁ : IsIso (α.app T.obj₁)) (h₃ : IsIso (α.app T.obj₃))
    (h₄ : IsIso (α.app (T.obj₁⟦(1 : ℤ)⟧))) : IsIso (α.app T.obj₂) := by
  let R (H : C ⥤ AddCommGrpCat.{v}) := ComposableArrows.mk₄
    (H.map T.invRotate.mor₁) (H.map T.mor₁) (H.map T.mor₂) (H.map T.mor₃)
  have hR (H : C ⥤ AddCommGrpCat.{v}) [H.IsHomological] : (R H).Exact := by
    apply ComposableArrows.exact_of_δ₀
    · exact (H.map_distinguished_exact _
        (Pretriangulated.inv_rot_of_distTriang _ hT)).exact_toComposableArrows
    · apply ComposableArrows.exact_of_δ₀
      · exact (H.map_distinguished_exact T hT).exact_toComposableArrows
      · exact (H.map_distinguished_exact _
          (Pretriangulated.rot_of_distTriang _ hT)).exact_toComposableArrows
  let φ : R F ⟶ R G := ComposableArrows.homMk₄
    (α.app _) (α.app _) (α.app _) (α.app _) (α.app _)
    (α.naturality _) (α.naturality _) (α.naturality _) (α.naturality _)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (hR F) (hR G) φ
    (inferInstanceAs (Epi (α.app (T.obj₃⟦(-1 : ℤ)⟧)))) h₁ h₃
    (inferInstanceAs (Mono (α.app (T.obj₁⟦(1 : ℤ)⟧))))

/-- Filtered Hom continuity is closed under distinguished extensions.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), long exact Hom sequence argument.
(auxiliary; not a blueprint node)

Proof: for a distinguished triangle A → B → C → A[1], take its contravariant
long exact additive Hom sequence into each Dᵢ[n] and into c.pt[n]. Filtered colimits
of abelian groups are exact. The cocone legs induce a morphism of the two exact
five-term windows with terms Hom(A,-[n-1]), Hom(C,-[n]), Hom(B,-[n]), Hom(A,-[n]),
and Hom(C,-[n+1]). The four outer vertical maps are invertible by the hypotheses
on A and C. The five lemma makes the middle map invertible, for every integer n. -/
theorem homColimitProperty_extensions (D : I ⥤ C) (c : Cocone D)
    (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C)
    (h₁ : homColimitProperty D c T.obj₁) (h₃ : homColimitProperty D c T.obj₃) :
    homColimitProperty D c T.obj₂ := by
  intro n
  let D' := D ⋙ shiftFunctor C n
  let c' := (shiftFunctor C n).mapCocone c
  let α := homColimitComparison D' c'
  let S := (Pretriangulated.triangleOpEquivalence C).functor.obj (op T)
  have hS : S ∈ distTriang Cᵒᵖ := Pretriangulated.op_distinguished T hT
  have hA : IsIso (α.app S.obj₃) := h₁ n
  have hC : IsIso (α.app S.obj₁) := h₃ n
  have hA' : IsIso (α.app (S.obj₃⟦(-1 : ℤ)⟧)) := by
    change IsIso (colimit.desc _
      ((preadditiveCoyoneda.obj (op (T.obj₁⟦(1 : ℤ)⟧))).mapCocone c'))
    exact homColimitProperty_shift D c T.obj₁ h₁ 1 n
  have hC' : IsIso (α.app (S.obj₁⟦(1 : ℤ)⟧)) := by
    change IsIso (colimit.desc _
      ((preadditiveCoyoneda.obj (op (T.obj₃⟦(-1 : ℤ)⟧))).mapCocone c'))
    exact homColimitProperty_shift D c T.obj₃ h₃ (-1) n
  exact iso_middle_of_homological _ _ α S hS hA' hC hA hC'

variable (D : I ⥤ C) (c : Cocone D)

/-- `homColimitProperty D c` is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_homColimitProperty :
    (homColimitProperty D c).IsClosedUnderIsomorphisms where
  of_iso e h n := desc_iso_transfer D c _ _
    (Functor.isoWhiskerLeft (shiftFunctor C n) (preadditiveCoyoneda.mapIso e.symm.op)) (h n)

/-- `homColimitProperty D c` is stable under shifts. -/
instance isStableUnderShift_homColimitProperty : (homColimitProperty D c).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K h ↦ homColimitProperty_shift D c K h n⟩

open ZeroObject in
/-- The objects whose shifted Hom functors carry the cocone `c` to a colimit form a triangulated
subcategory: they contain `0`, and are stable under shifts and extensions
(`homColimitProperty_extensions`). -/
instance isTriangulated_homColimitProperty : (homColimitProperty D c).IsTriangulated where
  exists_zero := by
    refine ⟨0, isZero_zero C, fun n ↦ ?_⟩
    have h (Y : C) : IsZero ((preadditiveCoyoneda.obj (op (0 : C))).obj Y) := by
      apply (IsZero.iff_id_eq_zero _).2
      ext f
      exact (isZero_zero C).eq_of_src _ _
    apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
    exact ⟨IsColimit.ofIsZero _ ((Functor.isZero_iff _).2 (fun i ↦ h _)) (h _)⟩
  toIsTriangulatedClosed₂ := .mk' (homColimitProperty_extensions D c)

end CategoryTheory
