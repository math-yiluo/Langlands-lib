/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Descent of a cochain augmentation computed on resolutions

Source: Stacks Project, Derived Categories, Tags 06XN and 05SU.
(blueprint: lem-cbc-cochain-augmentation-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- An augmentation which is invertible on resolving models identifies the localization of
its source functor with the derived target. The comparison uses the specified counit.

Source: Stacks Project, Derived Categories, Tags 06XN and 05SU
(blueprint: lem-cbc-cochain-augmentation-descent).

Proof: Localize H and its inclusion. Postcompose the pointwise universal counit with the
right adjoint V; it remains universal because right adjoints preserve limits. Lift the
localized augmentation through that universal counit. On resolving models both the counit
and the augmentation are invertible, so the lift is invertible. For any complex resolve it
and use naturality to transport this fact. Essential surjectivity of Q then gives an
isomorphism of functors. The universal factorization is the asserted component equation. -/
theorem exists_cochainAugmentationDescent
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (E : A ⥤ B) [E.Additive] (V : B ⥤ A) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))]
    [(E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
      (HomologicalComplex.quasiIso A (.up ℤ))]
    [V.mapDerivedCategory.IsRightAdjoint]
    (P : ObjectProperty (CochainComplex A ℤ))
    (hres : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), P L ∧ QuasiIso p)
    (hε : ∀ K, P K → IsIso (ε.app K))
    (H : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (j : 𝟭 (CochainComplex A ℤ) ⟶ H)
    (hH : ∀ {K L : CochainComplex A ℤ} (f : K ⟶ L), QuasiIso f → QuasiIso (H.map f))
    (a : H ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ V.mapHomologicalComplex (.up ℤ))
    (ha : ∀ K, P K → QuasiIso (a.app K)) :
    ∃ (D : DerivedCategory A ⥤ DerivedCategory A)
      (e : DerivedCategory.Q ⋙ D ≅ H ⋙ DerivedCategory.Q)
      (i : 𝟭 (DerivedCategory A) ⟶ D),
      (∀ K, i.app (DerivedCategory.Q.obj K) ≫ e.hom.app K =
        DerivedCategory.Q.map (j.app K)) ∧
      ∃ c : D ≅ F ⋙ V.mapDerivedCategory,
        ∀ K : CochainComplex A ℤ,
          c.hom.app (DerivedCategory.Q.obj K) ≫ V.mapDerivedCategory.map (ε.app K) ≫
            V.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) =
          e.hom.app K ≫ DerivedCategory.Q.map (a.app K) := by
  classical
  let Q := DerivedCategory.Q (C := A)
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let U := E.mapHomologicalComplex (.up ℤ)
  let Vc := V.mapHomologicalComplex (.up ℤ)
  let Vd := V.mapDerivedCategory
  let T := U ⋙ Vc ⋙ Q
  let k : (U ⋙ DerivedCategory.Q) ⋙ Vd ≅ T :=
    associator _ _ _ ≪≫ isoWhiskerLeft U V.mapDerivedCategoryFactors
  let δ₀ := (associator Q F Vd).inv ≫ whiskerRight ε Vd
  let δ : Q ⋙ (F ⋙ Vd) ⟶ T := δ₀ ≫ k.hom
  have : F.IsRightKanExtension ε :=
    IsLeftDerivedFunctor.isRightKanExtension F ε W
  have : HasPointwiseRightKanExtension Q (U ⋙ DerivedCategory.Q) :=
    hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor _ Q W
  have : (F ⋙ Vd).IsRightKanExtension δ₀ := by infer_instance
  have : (F ⋙ Vd).IsRightKanExtension δ :=
    (isRightKanExtension_iff_of_iso₂ δ₀ δ k (Iso.refl _) (by simp [δ])).1
      inferInstance
  have hinv : W.IsInvertedBy (H ⋙ Q) := by
    intro K L f hf
    have := hH f hf
    exact inferInstanceAs (IsIso (Q.map (H.map f)))
  let D := Localization.lift (H ⋙ Q) hinv Q
  let e := Localization.fac (H ⋙ Q) hinv Q
  let β : Q ⟶ H ⋙ Q := Q.leftUnitor.inv ≫ whiskerRight j Q
  let i : 𝟭 (DerivedCategory A) ⟶ D :=
    Localization.liftNatTrans Q W Q (H ⋙ Q) (𝟭 _) D β
  have hi (K : CochainComplex A ℤ) :
      i.app (Q.obj K) ≫ e.hom.app K = Q.map (j.app K) := by
    dsimp only [i]
    rw [Localization.liftNatTrans_app]
    change (𝟙 _ ≫ β.app K ≫ e.inv.app K) ≫ e.hom.app K = _
    simp [β]
  let γ : Q ⋙ D ⟶ T := e.hom ≫ whiskerRight a Q ≫ (associator U Vc Q).hom
  let c := (F ⋙ Vd).liftOfIsRightKanExtension δ D γ
  have hc (K : CochainComplex A ℤ) :
      c.app (Q.obj K) ≫ Vd.map (ε.app K) ≫
        V.mapDerivedCategoryFactors.hom.app (U.obj K) =
      e.hom.app K ≫ Q.map (a.app K) := by
    have h : c.app (Q.obj K) ≫ δ.app K = γ.app K :=
      (F ⋙ Vd).liftOfIsRightKanExtension_fac_app δ D γ K
    change c.app (Q.obj K) ≫
      ((𝟙 _ ≫ Vd.map (ε.app K)) ≫ 𝟙 _ ≫
        V.mapDerivedCategoryFactors.hom.app (U.obj K)) =
      e.hom.app K ≫ Q.map (a.app K) ≫ 𝟙 _ at h
    simpa only [Category.id_comp, Category.comp_id, Category.assoc] using h
  have hgood (K : CochainComplex A ℤ) (hK : P K) : IsIso (c.app (Q.obj K)) := by
    have := hε K hK
    have := ha K hK
    have he := hc K
    have : IsIso (c.app (Q.obj K) ≫ Vd.map (ε.app K) ≫
        V.mapDerivedCategoryFactors.hom.app (U.obj K)) := by
      rw [he]
      infer_instance
    exact (isIso_comp_right_iff (c.app (Q.obj K))
      (Vd.map (ε.app K) ≫ V.mapDerivedCategoryFactors.hom.app (U.obj K))).1 this
  have hobj (K : CochainComplex A ℤ) : IsIso (c.app (Q.obj K)) := by
    obtain ⟨L, p, hL, hp⟩ := hres K
    have := hgood L hL
    have : IsIso (Q.map p) := Localization.inverts Q W p hp
    have hn := c.naturality (Q.map p)
    rw [← isIso_comp_left_iff (D.map (Q.map p)), hn]
    infer_instance
  have : ∀ X, IsIso (c.app X) := by
    intro X
    let eX := Q.objObjPreimageIso X
    have := hobj (Q.objPreimage X)
    rw [← isIso_comp_left_iff (D.map eX.hom), c.naturality eX.hom]
    infer_instance
  have : IsIso c := NatIso.isIso_of_isIso_app c
  exact ⟨D, e, i, hi, asIso c, hc⟩

end CategoryTheory.Functor
