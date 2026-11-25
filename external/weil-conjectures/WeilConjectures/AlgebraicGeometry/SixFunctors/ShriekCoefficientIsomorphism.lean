/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences

/-!
# Coefficient-isomorphism transport of compactification functors

The comparison is constructed from the two canonical scalar-restriction comparisons.
All categories are the ordinary unbounded derived module-object categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']

attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar

/-- Termwise restriction along the inverse coefficient isomorphism. -/
noncomputable abbrev shriekCoefficientTransport (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :=
  (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap e.inv.hom T)).mapDerivedCategory

/-- The existing finite-constant-model, finite-Tor property, as an object property. -/
abbrev shriekCoefficientCtf (T : Scheme.{u}) :=
  constantModelBoundedConstructible Λ T ⊓ DerivedCategory.finiteTorAmplitude _

/-- The existing intersection-defined localizing closure, with coproducts indexed in
`Type (u + 1)`, the fixed ambient Hom universe. -/
abbrev shriekCoefficientLocalizing (T : Scheme.{u}) :=
  (shriekCoefficientCtf (Λ := Λ) T).localizingClosure

-- Keep the geometric pullback constructions opaque in categorical comparisons.
set_option backward.isDefEq.respectTransparency true

/-- The ambient canonical comparison, obtained by the direct-image comparison and
then the termwise open-extension comparison, with associators inserted. -/
noncomputable def shriekCoefficientCompactificationIso
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙
        shriekCoefficientTransport e Y ≅
      shriekCoefficientTransport e X ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ' c.obj.obj := by
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  letI (T : Scheme.{u}) : IsIso (coefficientMap e.inv.hom T) :=
    inferInstanceAs (IsIso ((upperStarFromPoint T).map e.inv.hom))
  letI (T : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv.hom T)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv
      (coefficientMap e.inv.hom T)).symm
  let J := CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i
  let J' := CondensedRing.openImmersionLowerShriek Λ' c.obj.obj.i
  let P := CondensedRing.lowerStar Λ c.obj.obj.g
  let P' := CondensedRing.lowerStar Λ' c.obj.obj.g
  let UZ := shriekCoefficientTransport e c.obj.obj.Z
  let d : P.rightDerivedFunctor ⋙ shriekCoefficientTransport e Y ≅
      UZ ⋙ P'.rightDerivedFunctor :=
    CondensedRing.derivedComapLowerStarIso e.inv.hom c.obj.obj.g
  let j : J.mapDerivedCategory ⋙ UZ ≅
      shriekCoefficientTransport e X ⋙ J'.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso J (Mod.comap
      (coefficientMap e.inv.hom c.obj.obj.Z)) ≪≫
      Functor.mapDerivedCategoryNatIso
        (CondensedRing.comapOpenImmersionLowerShriekIso e.inv.hom c.obj.obj.i) ≪≫
      (Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap e.inv.hom X)) J').symm
  exact Functor.associator J.mapDerivedCategory P.rightDerivedFunctor
      (shriekCoefficientTransport e Y) ≪≫
    Functor.isoWhiskerLeft J.mapDerivedCategory d ≪≫
    (Functor.associator J.mapDerivedCategory UZ P'.rightDerivedFunctor).symm ≪≫
    Functor.isoWhiskerRight j P'.rightDerivedFunctor ≪≫
    Functor.associator (shriekCoefficientTransport e X) J'.mapDerivedCategory
      P'.rightDerivedFunctor

private theorem localModel_iso {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (i : M ≅ N) (h : HasFiniteConstantLocalModel Λ T M) :
    HasFiniteConstantLocalModel Λ T N := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨j⟩⟩ := hU a
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f a)).mapIso i.symm ≪≫ j⟩⟩

private theorem stratified_iso {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (i : M ≅ N) (h : IsFiniteConstantStratified Λ T M) :
    IsFiniteConstantStratified Λ T N := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun a ↦ localModel_iso
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso i) (hS a)⟩

private theorem constructible_iso {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (i : M ≅ N) (h : IsConstantModelConstructible Λ T M) :
    IsConstantModelConstructible Λ T N := by
  classical
  unfold IsConstantModelConstructible at h ⊢
  split at h
  · rw [ite_eq_left ‹_›]
    exact stratified_iso i h
  · rw [ite_eq_right ‹_›]
    exact fun U hU ↦ stratified_iso
      ((CondensedRing.upperStar Λ U.ι).mapIso i) (h U hU)

-- Match the ambient tensor instance already fixed in `shriekCoefficientCtf`.
set_option backward.isDefEq.respectTransparency false in
private instance ctf_replete (T : Scheme.{u}) :
    (shriekCoefficientCtf (Λ := Λ) T).IsClosedUnderIsomorphisms where
  of_iso i h :=
    ⟨⟨ObjectProperty.prop_of_iso _ i h.1.1,
      fun n ↦ constructible_iso ((DerivedCategory.homologyFunctor _ n).mapIso i) (h.1.2 n)⟩,
      ObjectProperty.prop_of_iso _ i h.2⟩

private noncomputable def transportCompIso
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    shriekCoefficientTransport e T ⋙ shriekCoefficientTransport e.symm T ≅ 𝟭 _ := by
  exact Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp _ _).symm ≪≫ Mod.comapCongr (by
        change (upperStarFromPoint T).map e.hom.hom ≫
          (upperStarFromPoint T).map e.inv.hom = 𝟙 _
        rw [← Functor.map_comp]
        change (upperStarFromPoint T).map ((Mon.forget _).map (e.hom ≫ e.inv)) = _
        simp only [Iso.hom_inv_id]
        exact (upperStarFromPoint T).map_id Λ) ≪≫ Mod.comapId _) ≪≫
    Functor.mapDerivedCategoryIdIso _

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
private theorem transport_equivalence (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    (shriekCoefficientTransport e T).IsEquivalence := by
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have : IsIso (coefficientMap e.inv.hom T) :=
    inferInstanceAs (IsIso ((upperStarFromPoint T).map e.inv.hom))
  have : (Mod.comap (coefficientMap e.inv.hom T)).IsEquivalence :=
    (inferInstance : (Mod.comapEquivalenceOfIsIso
      (coefficientMap e.inv.hom T)).functor.IsEquivalence)
  exact Functor.isEquivalence_mapDerivedCategory _

private theorem transport_ctf (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    ∀ K, shriekCoefficientCtf (Λ := Λ') T ((shriekCoefficientTransport e T).obj K) ↔
      shriekCoefficientCtf (Λ := Λ) T K := by
  intro K
  constructor
  · intro h
    exact ObjectProperty.prop_of_iso _ ((transportCompIso e T).app K)
      (constantModelCtf_coefficientIso e.symm T
        ⟨(shriekCoefficientTransport e T).obj K, h⟩)
  · intro h
    exact constantModelCtf_coefficientIso e T ⟨K, h⟩

private theorem map_closure
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (h : ∀ K, P K → Q (F.obj K)) :
    ∀ K, P.localizingClosure K → Q.localizingClosure (F.obj K) := by
  have : (Q.localizingClosure.inverseImage F).IsLocalizing :=
    { isClosedUnderColimitsOfShape_discrete := fun _ ↦ inferInstance }
  exact ObjectProperty.localizingClosure_le
    (Q := Q.localizingClosure.inverseImage F)
    (fun K hK ↦ Q.le_localizingClosure _ (h K hK))

/-- Exact scalar transport identifies both the constructible classes and their closures. -/
theorem shriekCoefficientIso_transport (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    (shriekCoefficientTransport e T).IsEquivalence ∧
    (shriekCoefficientTransport e T).IsTriangulated ∧
    (∀ I : Type (u + 1),
      PreservesColimitsOfShape (Discrete I) (shriekCoefficientTransport e T)) ∧
    (∀ K, shriekCoefficientCtf (Λ := Λ') T ((shriekCoefficientTransport e T).obj K) ↔
      shriekCoefficientCtf (Λ := Λ) T K) ∧
    (∀ K, shriekCoefficientLocalizing (Λ := Λ') T
        ((shriekCoefficientTransport e T).obj K) ↔
      shriekCoefficientLocalizing (Λ := Λ) T K) := by
  have := transport_equivalence e T
  have := transport_equivalence e.symm T
  refine ⟨inferInstance, inferInstance, fun _ ↦ inferInstance, transport_ctf e T, ?_⟩
  intro K
  constructor
  · intro h
    exact ObjectProperty.prop_of_iso _ ((transportCompIso e T).app K)
      (map_closure (shriekCoefficientTransport e.symm T)
        (shriekCoefficientCtf (Λ := Λ') T) (shriekCoefficientCtf (Λ := Λ) T)
        (fun L hL ↦ (transport_ctf e.symm T L).2 hL) _ h)
  · exact map_closure (shriekCoefficientTransport e T)
      (shriekCoefficientCtf (Λ := Λ) T) (shriekCoefficientCtf (Λ := Λ') T)
      (fun L hL ↦ (transport_ctf e T L).2 hL) K

end AlgebraicGeometry.ProEtale
