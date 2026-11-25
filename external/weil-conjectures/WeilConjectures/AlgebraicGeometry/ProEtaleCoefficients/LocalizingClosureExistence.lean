/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.GrothendieckDerivedCoproductsColimit

import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
/-!
# Existence and thickness of the localizing closure

Coefficients are arbitrary condensed rings, including noncommutative rings. The
module category is Mathlib's category of internal left modules over the actual
pulled-back ring object. Index sets live in `Type (u + 1)`; the larger universe
of the type of all module objects does not enlarge the required coproduct existence.

## Implementation details

`localizingClosure` is the intersection of all localizing subcategories containing `S`. Its
localizing predicate asks for closure under all existing coproducts in the object universe;
this agrees with closure under `Type (u + 1)`-indexed coproducts, since the Hom types live in
that universe and an existing larger coproduct has only that many nonzero summands.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

open Opposite CategoryTheory.Pretriangulated.Opposite

private noncomputable def cofanUnopIsColimit
    {C : Type u} [Category.{v} C] {I : Type w} (F : I → Cᵒᵖ) [HasProduct F] :
    IsColimit (Cofan.mk (∏ᶜ F).unop (fun i ↦ (Pi.π F i).unop)) := by
  let hc := productIsProduct F
  refine Cofan.IsColimit.mk _
    (fun s ↦ (hc.lift (Fan.mk (op s.pt) (fun i ↦ (s.inj i).op))).unop) ?_ ?_
  · intro s i
    apply Quiver.Hom.op_inj
    exact hc.fac (Fan.mk (op s.pt) (fun i ↦ (s.inj i).op)) (Discrete.mk i)
  · intro s m hm
    apply Quiver.Hom.op_inj
    apply hc.hom_ext
    intro ⟨i⟩
    exact (congrArg Quiver.Hom.op (hm i)).trans
      (hc.fac (Fan.mk (op s.pt) (fun i ↦ (s.inj i).op)) (Discrete.mk i)).symm

private theorem triangleCoproducts
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasCoproducts.{w} C] (I : Type w) (T : I → Triangle C)
    (hT : ∀ i, T i ∈ distTriang C) :
    ∃ c : Cofan T,
      Nonempty (IsColimit (Triangle.π₁.mapCocone c)) ∧
      Nonempty (IsColimit (Triangle.π₂.mapCocone c)) ∧
      Nonempty (IsColimit (Triangle.π₃.mapCocone c)) ∧ c.pt ∈ distTriang C := by
  classical
  let e := triangleOpEquivalence C
  let T' : I → Triangle Cᵒᵖ := fun i ↦ e.functor.obj (op (T i))
  let U := productTriangle T'
  let Z := (e.inverse.obj U).unop
  let c : Cofan T := Cofan.mk Z (fun i ↦
    ((e.unitIso.app (op (T i))).unop).inv ≫
      (e.inverse.map (productTriangle.π T' i)).unop)
  refine ⟨c, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ?_⟩
  · refine (isColimitMapCoconeCofanMkEquiv Triangle.π₁ T _).symm ?_
    refine IsColimit.ofIsoColimit (cofanUnopIsColimit (fun i ↦ (T' i).obj₃))
      (Cocone.ext (Iso.refl _) ?_)
    intro ⟨i⟩
    change (Pi.π (fun i ↦ (T' i).obj₃) i).unop ≫ 𝟙 _ =
      𝟙 _ ≫ (Pi.π (fun i ↦ (T' i).obj₃) i).unop
    simp only [Category.id_comp, Category.comp_id]
  · refine (isColimitMapCoconeCofanMkEquiv Triangle.π₂ T _).symm ?_
    refine IsColimit.ofIsoColimit (cofanUnopIsColimit (fun i ↦ (T' i).obj₂))
      (Cocone.ext (Iso.refl _) ?_)
    intro ⟨i⟩
    change (Pi.π (fun i ↦ (T' i).obj₂) i).unop ≫ 𝟙 _ =
      𝟙 _ ≫ (Pi.π (fun i ↦ (T' i).obj₂) i).unop
    simp only [Category.id_comp, Category.comp_id]
  · refine (isColimitMapCoconeCofanMkEquiv Triangle.π₃ T _).symm ?_
    refine IsColimit.ofIsoColimit (cofanUnopIsColimit (fun i ↦ (T' i).obj₁))
      (Cocone.ext (Iso.refl _) ?_)
    intro ⟨i⟩
    change (Pi.π (fun i ↦ (T' i).obj₁) i).unop ≫ 𝟙 _ =
      𝟙 _ ≫ (Pi.π (fun i ↦ (T' i).obj₁) i).unop
    simp only [Category.id_comp, Category.comp_id]
  · exact unop_distinguished U (productTriangle_distinguished T'
      (fun i ↦ op_distinguished (T i) (hT i)))

private theorem derivedCoproductCocone
    (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{t} A] (I : Type w) (K : I → CochainComplex A ℤ) :
    ∃ c : Cofan K,
      (∀ n : ℤ, Nonempty (IsColimit ((HomologicalComplex.eval _ _ n).mapCocone c))) ∧
      Nonempty (IsColimit (DerivedCategory.Q.mapCocone c)) := by
  let : HasColimitsOfSize.{w, w} A := IsGrothendieckAbelian.hasColimits A
  refine ⟨HomologicalComplex.coconeOfHasColimitEval (Discrete.functor K), ?_, ?_⟩
  · exact fun n ↦ ⟨colimit.isColimit _⟩
  · exact DerivedCategory.isColimit_mapCocone_grothendieckSum A I K

/-- The derived category of condensed-coefficient modules has `Type (u + 1)`-indexed
coproducts, computed termwise on complexes, and coproducts of distinguished triangles are
distinguished; moreover `localizingClosure S` is the smallest localizing subcategory
containing `S` (for an arbitrary, not necessarily small, class `S`), it is closed under
retracts, and it does not change when `S` is enlarged inside it. -/
theorem localizingClosure_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u})
    [HasDerivedCategory.{u + 1}
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))]
    (S : ObjectProperty (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) :
    HasCoproducts.{u + 1} (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) ∧
    (∀ (I : Type (u + 1))
      (K : I → CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ),
      ∃ c : Cofan K,
        (∀ n : ℤ, Nonempty (IsColimit
          ((HomologicalComplex.eval _ _ n).mapCocone c))) ∧
        Nonempty (IsColimit (DerivedCategory.Q.mapCocone c))) ∧
    (∀ (I : Type (u + 1))
      (T : I → Triangle (DerivedCategory
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))),
      (∀ i : I, T i ∈ distTriang _) →
      ∃ c : Cofan T,
        Nonempty (IsColimit (Triangle.π₁.mapCocone c)) ∧
        Nonempty (IsColimit (Triangle.π₂.mapCocone c)) ∧
        Nonempty (IsColimit (Triangle.π₃.mapCocone c)) ∧
        c.pt ∈ distTriang _) ∧
    IsLocalizingSubcategory (localizingClosure S) ∧
    (S ≤ localizingClosure S) ∧
    (∀ P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      IsLocalizingSubcategory P → S ≤ P →
        localizingClosure S ≤ P) ∧
    (localizingClosure S).IsStableUnderRetracts ∧
    (∀ S' : ObjectProperty (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      S ≤ S' → S' ≤ localizingClosure S →
        localizingClosure S' = localizingClosure S) := by
  classical
  let A := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let : IsGrothendieckAbelian.{u + 1} A := Mod.isGrothendieckAbelian _
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  let : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  let : HasCoproducts.{u + 1} A :=
    fun I ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  let : HasCoproducts.{u + 1} (DerivedCategory A) := derived_hasCoproducts
  have hiso : (localizingClosure S).IsClosedUnderIsomorphisms := by
    constructor
    intro K L e hK P hP hS
    let := hP.2.1
    exact P.prop_of_iso e (hK P hP hS)
  let := hiso
  have hzero : (localizingClosure S).ContainsZero := by
    refine ⟨0, isZero_zero _, ?_⟩
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.prop_zero
  let := hzero
  have hshift : (localizingClosure S).IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro K hK
    rw [ObjectProperty.prop_shift_iff]
    intro P hP hS
    let := hP.1
    exact P.le_shift n K (hK P hP hS)
  let := hshift
  have htri : (localizingClosure S).IsTriangulated := by
    refine { ext₂' := ?_ }
    intro T hT h₁ h₃
    apply ObjectProperty.le_isoClosure
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hS) (h₃ P hP hS)
  let := htri
  have hloc : IsLocalizingSubcategory (localizingClosure S) := by
    refine ⟨htri, hiso, ?_⟩
    intro I F hF hK
    change ∀ P, IsLocalizingSubcategory P → S ≤ P → _
    intro P hP hS
    exact hP.2.2 F hF (fun i ↦ hK i P hP hS)
  have hcontains : S ≤ localizingClosure S := fun K hK P hP hS ↦ hS K hK
  have hminimal : ∀ P, IsLocalizingSubcategory P → S ≤ P → localizingClosure S ≤ P :=
    fun P hP hS K hK ↦ hK P hP hS
  refine ⟨inferInstance, ?_, ?_, hloc, hcontains, hminimal, ?_, ?_⟩
  · intro I K
    exact derivedCoproductCocone A I K
  · exact triangleCoproducts
  · let P := localizingClosure S
    let (I : Type (u + 1)) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
      apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
      rintro _ ⟨F, hF⟩
      exact hloc.prop_colimit F inferInstance (fun i ↦ hF ⟨i⟩)
    let : HasCoproducts.{u + 1} P.FullSubcategory := fun I ↦
      hasColimitsOfShape_of_closedUnderColimits (Discrete I) P
    let : IsIdempotentComplete P.FullSubcategory :=
      isIdempotentComplete_of_countableCoproducts P.FullSubcategory
    constructor
    intro K L r hL
    let L' : P.FullSubcategory := ⟨L, hL⟩
    let p : L' ⟶ L' := ObjectProperty.homMk (r.r ≫ r.i)
    -- Split the retract idempotent within the full localizing subcategory.
    have hp : p ≫ p = p := by
      apply ObjectProperty.hom_ext
      simp [p, Category.assoc]
    obtain ⟨K', i, e, hie, hei⟩ := IsIdempotentComplete.idempotents_split L' p hp
    have hie' : i.hom ≫ e.hom = 𝟙 K'.obj := congrArg (fun f ↦ f.hom) hie
    have hei' : e.hom ≫ i.hom = r.r ≫ r.i := congrArg (fun f ↦ f.hom) hei
    let a : K ≅ K'.obj :=
      { hom := r.i ≫ e.hom
        inv := i.hom ≫ r.r
        hom_inv_id := by rw [Category.assoc, ← Category.assoc e.hom, hei']; simp
        inv_hom_id := by
          calc
            _ = (i.hom ≫ (r.r ≫ r.i)) ≫ e.hom := by simp only [Category.assoc]
            _ = (i.hom ≫ (e.hom ≫ i.hom)) ≫ e.hom := by rw [hei']
            _ = 𝟙 K'.obj := by
              simp only [← Category.assoc, hie', Category.id_comp] }
    exact P.prop_of_iso a.symm K'.property
  · intro S' h₁ h₂
    apply le_antisymm
    · intro K hK
      exact hK (localizingClosure S) hloc h₂
    · intro K hK P hP hSP
      exact hK P hP (fun L hL ↦ hSP L (h₁ L hL))

end AlgebraicGeometry.ProEtale
