/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedExchangeComparison
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Native proper base change on affine base charts
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem encoding_bridge (l : ℕ) [Fact l.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l)) (X : Scheme.{u})
    (M : DerivedCategory (AdicSheaf l X))
    (h : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) X)
      ((nativeExchangeEncoding l X).mapDerivedCategory.obj M)) :
    boundedConstructible (condensedRingObj Λ.X X)
      ((nativeExchangeEncodingAt l Λ hΛ X).mapDerivedCategory.obj M) := by
  subst Λ
  simpa only [nativeExchangeEncodingAt] using h

attribute [local irreducible] DerivedCategory HasDerivedCategory.standard
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CondensedRing.boundedConstructibleBaseChangeOfPreserves
  upperStarFromPoint Functor.leftDerivedFunctor Mod.monoidalCategory
  CondensedRing.boundedConstructibleUpperStar
  CondensedRing.derivedUpperStarLowerStarAdjunction ObjectProperty.lift
  CondensedRing.boundedConstructibleUpperStarCompatibility
  CondensedRing.boundedConstructiblePullbackSquareComparison
  Functor.squareTransport Adjunction.restrictFullyFaithful

private theorem encoded_boundedConstructible
    (k₀ k : Type u) [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k]
    [IsAlgClosure k₀ k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsLocallyNoetherian X] [CompactSpace X]
    (M : DerivedCategory (AdicSheaf l X))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hc : ∀ n : ℤ, IsAdicConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ n).obj M)) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) X)
      ((nativeExchangeEncoding l X).mapDerivedCategory.obj M) := by
  let R := Profinite.padicAlgClRingObj.{u} l
  let F := nativeExchangeEncoding l X
  obtain ⟨E, hE, _, _, _, _, hCons, _⟩ :=
    nativeModuleConstructibilityComparison k₀ k l (Ne.symm (Fact.out : ringChar k₀ ≠ l)) X
  rw [hE] at hCons
  have hPred := adicConstructibilityPredicateComparison l X R (.algebraicClosure)
  have hF (N : AdicSheaf l X) : IsAdicConstructibleSheaf N →
      IsConstructibleModuleObject (condensedRingObj R X) (F.obj N) := by
    intro hN
    apply (hPred.1 _).mpr
    have hn := (hCons N).mp hN
    let e := (nativeOrdinaryPresentation l X).unitIso.symm.app (F.obj N)
    have hn' := (hPred.1 _).mpr hn
    apply (hPred.1 _).mp
    apply _root_.constructible_of_iso e
    simpa only [F, nativeExchangeEncoding, nativeToOrdinaryModules, Functor.comp_obj] using hn'
  refine ⟨F.bounded_mapDerivedCategory_obj hM, fun n ↦ ?_⟩
  exact _root_.constructible_of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app M)
    (hF _ (hc n))

private theorem reflect_native_iso (l : ℕ) [Fact l.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l)) (Y : Scheme.{u})
    {A B : DerivedCategory (AdicSheaf l Y)} (f : A ⟶ B)
    (hf : IsIso ((nativeExchangeEncodingAt l Λ hΛ Y).mapDerivedCategory.map f)) : IsIso f := by
  exact @isIso_of_reflects_iso _ _ _ _ _ _ f
    (nativeExchangeEncodingAt l Λ hΛ Y).mapDerivedCategory hf inferInstance

private theorem rational_component
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom]
    [QuasiCompact X'.hom]
    [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom]
    [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom]
    [QuasiCompact Y'.hom]
    [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom]
    [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [IsProper p.left] (sq : IsPullback v p' p g)
    (K : BoundedConstructible (condensedRingObj Λ.X X.left)) :
    IsIso (nativeUnderlyingExchangeArrow
      (boundedConstructible (condensedRingObj Λ.X Y'.left))
      ((CondensedRing.boundedConstructibleBaseChangeOfPreserves Λ.X l
        (CondensedRing.rationalCoefficientPushforwardPreservation l Λ (Or.inr hΛ))
        sq.toCommSq).app K)).hom := by
  exact nativeUnderlyingExchangeArrow_isIso
    (boundedConstructible (condensedRingObj Λ.X Y'.left))
    ((CondensedRing.boundedConstructibleBaseChangeOfPreserves Λ.X l
      (CondensedRing.rationalCoefficientPushforwardPreservation l Λ (Or.inr hΛ))
      sq.toCommSq).app K)
    (CondensedRing.isIso_properBaseChange_boundedConstructible_rational l
      p Λ (Or.inr hΛ) sq K)

private theorem proper_from_encoded
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom]
    [QuasiCompact X'.hom]
    [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom]
    [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom]
    [QuasiCompact Y'.hom]
    [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom]
    [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [IsProper p.left] (sq : IsPullback v p' p g) (M : DerivedCategory (AdicSheaf l X.left))
    (K : BoundedConstructible (condensedRingObj Λ.X X.left))
    (e : (nativeExchangeEncodingAt l Λ hΛ X.left).mapDerivedCategory.obj M ≅ K.obj) :
    IsIso ((adicDerivedBaseChange l
      ((Over.forget (Spec (CommRingCat.of k))).map_commSq sq.toCommSq)).app M) := by
  obtain ⟨a⟩ := nativeDerivedExchange_condensed_comparison l k Λ hΛ sq M K e
  have hi := rational_component l k Λ hΛ sq K
  exact reflect_native_iso l Λ hΛ Y'.left ((adicDerivedBaseChange l
      ((Over.forget (Spec (CommRingCat.of k))).map_commSq sq.toCommSq)).app M)
    ((Arrow.isIso_iff_isIso_of_isIso a.hom).mpr hi)

private theorem proper_from_encoded_bound
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom]
    [QuasiCompact X'.hom]
    [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom]
    [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom]
    [QuasiCompact Y'.hom]
    [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom]
    [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [IsProper p.left] (sq : IsPullback v p' p g) (M : DerivedCategory (AdicSheaf l X.left))
    (hM : boundedConstructible (condensedRingObj Λ.X X.left)
      ((nativeExchangeEncodingAt l Λ hΛ X.left).mapDerivedCategory.obj M)) :
    IsIso ((adicDerivedBaseChange l
      ((Over.forget (Spec (CommRingCat.of k))).map_commSq sq.toCommSq)).app M) := by
  exact proper_from_encoded l k Λ hΛ sq M
    ⟨(nativeExchangeEncodingAt l Λ hΛ X.left).mapDerivedCategory.obj M, hM⟩ (Iso.refl _)

/-- Proper base change on an affine chart over the algebraic closure of a finite field. -/
theorem adicDerivedBaseChange_isIso_of_affine
    (k₀ k : Type u) [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k]
    [IsAlgClosure k₀ k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {X' X Y' Y : Scheme.{u}}
    [X'.Over (Spec (CommRingCat.of k))] [X.Over (Spec (CommRingCat.of k))]
    [Y'.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [v.IsOver (Spec (CommRingCat.of k))] [p'.IsOver (Spec (CommRingCat.of k))]
    [p.IsOver (Spec (CommRingCat.of k))] [g.IsOver (Spec (CommRingCat.of k))]
    [IsAffine Y] [IsAffine Y']
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k))]
    [IsProper p] (sq : IsPullback v p' p g)
    (M : DerivedCategory (AdicSheaf l X))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hc : ∀ n : ℤ, IsAdicConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ n).obj M)) :
    IsIso ((adicDerivedBaseChange l sq.toCommSq).app M) := by
  let S := Spec (CommRingCat.of k)
  have : IsProper p' := MorphismProperty.of_isPullback sq (inferInstance : IsProper p)
  have : IsSeparated (Y ↘ S) := inferInstance
  have : IsSeparated (Y' ↘ S) := inferInstance
  have : QuasiCompact (Y ↘ S) := inferInstance
  have : QuasiCompact (Y' ↘ S) := inferInstance
  have : LocallyOfFiniteType (X ↘ S) := by
    rw [← comp_over p S]
    infer_instance
  have : LocallyOfFiniteType (X' ↘ S) := by
    rw [← comp_over p' S]
    infer_instance
  have : IsSeparated (X ↘ S) := by
    rw [← comp_over p S]
    infer_instance
  have : IsSeparated (X' ↘ S) := by
    rw [← comp_over p' S]
    infer_instance
  have : QuasiCompact (X ↘ S) := by
    rw [← comp_over p S]
    infer_instance
  have : QuasiCompact (X' ↘ S) := by
    rw [← comp_over p' S]
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ S)
  have : Fact (ringChar k).Prime :=
    ⟨by rw [← Algebra.ringChar_eq k₀ k]; exact CharP.prime_ringChar k₀⟩
  have : Fact (ringChar k ≠ l) :=
    ⟨by rw [← Algebra.ringChar_eq k₀ k]; exact Fact.out⟩
  have hK := encoded_boundedConstructible k₀ k l X M hM hc
  have : IsProper (p.asOver S).left := inferInstanceAs (IsProper p)
  exact proper_from_encoded_bound l k (Mon.mk (Profinite.padicAlgClRingObj l)) rfl
    (sq.asOver S) M
    (encoding_bridge l (Mon.mk (Profinite.padicAlgClRingObj l)) rfl X M hK)

end AlgebraicGeometry.ProEtale
