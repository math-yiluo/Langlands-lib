/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeBaseChange.GeometricProperBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Native.NativeBaseChangeOpenChart
import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedExchangeComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleSmoothBaseChange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The geometric native derived smooth base-change mate

For a cartesian square of `k₀`-schemes
```
Z' --v--> Z
|p'       |p
v         v
T' --g--> T
```
with `g` smooth and `p` separated, quasi-compact and locally of finite type, the native derived
base-change morphism `ḡ^* Rp̄_* ⟶ Rp̄'_* v̄^*` of the geometric square (the base change to the
algebraic closure of `k₀`) is invertible on bounded complexes with constructible cohomology
(`AlgebraicGeometry.NativeBaseChange.geometric_smooth_baseChange_isIso`).

## Implementation details

As for `AlgebraicGeometry.NativeBaseChange.geometric_proper_baseChange_isIso`, by the joint
conservativity of restriction to an affine Zariski cover of the target, the claim reduces to
affine charts
(`AlgebraicGeometry.ProEtale.adicDerivedBaseChange_isIso_of_affine_of_smooth`),
where the encoded native mate is identified with the condensed base-change morphism of bounded
constructible `ℚ̄_ℓ`-complexes, which is invertible by smooth base change
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_smooth`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

namespace ProEtale

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
    (hf : IsIso ((nativeExchangeEncodingAt l Λ hΛ Y).mapDerivedCategory.map f)) : IsIso f :=
  @isIso_of_reflects_iso _ _ _ _ _ _ f
    (nativeExchangeEncodingAt l Λ hΛ Y).mapDerivedCategory hf inferInstance

/-- The base-change morphism attached to the rational `ℚ̄_ℓ`-preservation proof is the standard
`ℚ̄_ℓ`-coefficient base-change morphism. -/
private theorem baseChange_restriction_eq (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Y X' Y' : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (H : CondensedRing.PreservesBoundedConstructiblePushforwards
      (Profinite.padicAlgClRingObj l) k)
    (sq : CommSq g' p' p g) :
    CondensedRing.boundedConstructibleBaseChangeOfPreserves (Profinite.padicAlgClRingObj l) l
      H sq = CondensedRing.boundedConstructibleBaseChange l sq := by
  rw [CondensedRing.boundedConstructibleBaseChange_def]
  with_unfolding_all rfl

/-- Smooth base change for the base-change morphism attached to any preservation proof for
`ℚ̄_ℓ`-coefficients. -/
private theorem isIso_baseChangeOfPreserves_of_smooth (l : ℕ) [Fact l.Prime] {k : Type u}
    [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (H : CondensedRing.PreservesBoundedConstructiblePushforwards
      (Profinite.padicAlgClRingObj l) k)
    [Smooth g.left] (sq : IsPullback v p' p g) :
    IsIso (CondensedRing.boundedConstructibleBaseChangeOfPreserves
      (Profinite.padicAlgClRingObj l) l H sq.toCommSq) := by
  rw [baseChange_restriction_eq]
  have (K : _) : IsIso ((CondensedRing.boundedConstructibleBaseChange l sq.toCommSq).app K) :=
    CondensedRing.isIso_boundedConstructibleBaseChange_of_smooth l sq K
  exact NatIso.isIso_of_isIso_app _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Smooth base change for the base-change morphism attached to the rational preservation proof
at a coefficient object equal to `ℚ̄_ℓ`. -/
private theorem isIso_rationalBaseChange_of_smooth
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [Smooth g.left] (sq : IsPullback v p' p g) :
    IsIso (CondensedRing.boundedConstructibleBaseChangeOfPreserves Λ.X l
        (CondensedRing.rationalCoefficientPushforwardPreservation l Λ (Or.inr hΛ))
        sq.toCommSq) := by
  have hΛ' := hΛ
  subst Λ
  have hstd : IsIso (CondensedRing.boundedConstructibleBaseChangeOfPreserves _ l
      (CondensedRing.rationalCoefficientPushforwardPreservation l _ (Or.inr hΛ'))
      sq.toCommSq) := by
    have h := isIso_baseChangeOfPreserves_of_smooth l
      (CondensedRing.rationalFinitenessPushforwardPreservation l) sq
    exact h
  exact hstd

private theorem smooth_rational_component
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [Smooth g.left] (sq : IsPullback v p' p g)
    (K : BoundedConstructible (condensedRingObj Λ.X X.left)) :
    IsIso (nativeUnderlyingExchangeArrow
      (boundedConstructible (condensedRingObj Λ.X Y'.left))
      ((CondensedRing.boundedConstructibleBaseChangeOfPreserves Λ.X l
        (CondensedRing.rationalCoefficientPushforwardPreservation l Λ (Or.inr hΛ))
        sq.toCommSq).app K)).hom := by
  have := isIso_rationalBaseChange_of_smooth l k Λ hΛ sq
  exact nativeUnderlyingExchangeArrow_isIso _ _ inferInstance

private theorem smooth_from_encoded
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [Smooth g.left] (sq : IsPullback v p' p g) (M : DerivedCategory (AdicSheaf l X.left))
    (hM : boundedConstructible (condensedRingObj Λ.X X.left)
      ((nativeExchangeEncodingAt l Λ hΛ X.left).mapDerivedCategory.obj M)) :
    IsIso ((adicDerivedBaseChange l
      ((Over.forget (Spec (CommRingCat.of k))).map_commSq sq.toCommSq)).app M) := by
  obtain ⟨a⟩ := nativeDerivedExchange_condensed_comparison l k Λ hΛ sq M
    ⟨(nativeExchangeEncodingAt l Λ hΛ X.left).mapDerivedCategory.obj M, hM⟩ (Iso.refl _)
  exact reflect_native_iso l Λ hΛ Y'.left _
    ((Arrow.isIso_iff_isIso_of_isIso a.hom).mpr (smooth_rational_component l k Λ hΛ sq _))

/-- Smooth base change on an affine chart over an algebraic closure `k` of a finite field: for
a cartesian square
```
X' --v--> X
|p'       |p
v         v
Y' --g--> Y
```
of `k`-schemes with `Y`, `Y'` affine of finite type over `k`, `g` smooth and `p` separated,
quasi-compact and locally of finite type, the native derived base-change morphism is invertible
on bounded complexes with constructible cohomology. -/
theorem adicDerivedBaseChange_isIso_of_affine_of_smooth
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
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [Smooth g]
    (sq : IsPullback v p' p g)
    (M : DerivedCategory (AdicSheaf l X))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hc : ∀ n : ℤ, IsAdicConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ n).obj M)) :
    IsIso ((adicDerivedBaseChange l sq.toCommSq).app M) := by
  let S := Spec (CommRingCat.of k)
  have : IsSeparated p' := MorphismProperty.of_isPullback sq (inferInstance : IsSeparated p)
  have : QuasiCompact p' := MorphismProperty.of_isPullback sq (inferInstance : QuasiCompact p)
  have : LocallyOfFiniteType p' :=
    MorphismProperty.of_isPullback sq (inferInstance : LocallyOfFiniteType p)
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
  have : Smooth (g.asOver S).left := inferInstanceAs (Smooth g)
  exact smooth_from_encoded l k (Mon.mk (Profinite.padicAlgClRingObj l)) rfl
    (sq.asOver S) M
    (encoding_bridge l (Mon.mk (Profinite.padicAlgClRingObj l)) rfl X M hK)
end ProEtale

namespace NativeBaseChange

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]

variable {Z' Z T' T : Scheme.{u}}
  [Z'.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [T'.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
  {v : Z' ⟶ Z} {p' : Z' ⟶ T'} {p : Z ⟶ T} {g : T' ⟶ T}
  [v.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
  [p.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]

omit [Finite k₀] in
/-- The base change to the algebraic closure of `k₀` of a cartesian square of `k₀`-schemes is
cartesian. -/
private theorem isPullback_geometricSquare (sq : IsPullback v p' p g) :
    IsPullback (geometricMap k₀ v) (geometricMap k₀ p')
      (geometricMap k₀ p) (geometricMap k₀ g) := by
  have hb := ((sq.asOver (Spec (CommRingCat.of k₀))).map
    (Over.pullback (Scheme.specAlgebraicClosure k₀).hom)).map
      (Over.forget (Spec (CommRingCat.of (AlgebraicClosure k₀))))
  simpa [geometricMap, Scheme.Hom.geometricFiberMap, Scheme.Hom.geometricFiber,
    Over.pullback, pullback.map, OverClass.asOver, CategoryTheory.over] using hb

/-- Smooth base change for the native derived base-change morphism of a cartesian square over
an algebraically closed field `k`, with `g` smooth and `p` separated, quasi-compact and locally of
finite type. -/
private theorem affineChart_descent_of_smooth
    (k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosure k₀ k]
    [Fact (ringChar k₀ ≠ l)]
    {X' X Y' Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
    [Y'.Over (Spec (CommRingCat.of k))]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [g.IsOver (Spec (CommRingCat.of k))] [IsSeparated p] [QuasiCompact p]
    [LocallyOfFiniteType p] [Smooth g]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k))]
    (sq : IsPullback v p' p g) (M : DerivedCategory (ProEtale.AdicSheaf l X))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hc : ∀ n : ℤ, ProEtale.IsAdicConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ n).obj M)) :
    IsIso ((ProEtale.adicDerivedBaseChange l sq.toCommSq).app M) := by
  let U := Y.affineCover.pullback₁ g
  let C := U.bind fun a ↦ (U.X a).affineCover
  apply ProEtale.isIso_of_isIso_mapDerivedCategory_adicUpperStar l C.f
    (Scheme.zariskiPrecoverage_le_proetalePrecoverage _ C.mem₀)
  rintro ⟨a, b⟩
  change Y.affineCover.I₀ at a
  change (pullback g (Y.affineCover.f a)).affineCover.I₀ at b
  let A := Y.affineCover.X a
  let i := Y.affineCover.f a
  let V := (pullback g i).affineCover
  let B := V.X b
  let j := V.f b ≫ pullback.fst g i
  let h := V.f b ≫ pullback.snd g i
  have w : h ≫ i = j ≫ g := by
    dsimp only [h, j]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  let S := Spec (CommRingCat.of k)
  let : A.Over S := ⟨i ≫ (Y ↘ S)⟩
  let : B.Over S := ⟨j ≫ (Y' ↘ S)⟩
  let : (pullback p i).Over S := ⟨pullback.snd p i ≫ (A ↘ S)⟩
  let : (pullback (pullback.snd p i) h).Over S :=
    ⟨pullback.snd (pullback.snd p i) h ≫ (B ↘ S)⟩
  have : h.IsOver S := ⟨by
    change h ≫ (i ≫ (Y ↘ S)) = j ≫ (Y' ↘ S)
    rw [← Category.assoc, w, Category.assoc, comp_over g S]⟩
  have : (pullback.snd p i).IsOver S := ⟨rfl⟩
  have : (pullback.snd (pullback.snd p i) h).IsOver S := ⟨rfl⟩
  have : (pullback.fst (pullback.snd p i) h).IsOver S := ⟨by
    change pullback.fst _ _ ≫ (pullback.snd p i ≫ (A ↘ S)) =
      pullback.snd _ _ ≫ (B ↘ S)
    rw [← Category.assoc, pullback.condition, Category.assoc, comp_over h S]⟩
  have : IsAffine A := inferInstanceAs (IsAffine (Y.affineCover.X a))
  have : IsAffine B := inferInstanceAs (IsAffine (V.X b))
  have : LocallyOfFiniteType (A ↘ S) :=
    inferInstanceAs (LocallyOfFiniteType (i ≫ (Y ↘ S)))
  have : LocallyOfFiniteType (B ↘ S) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ (Y' ↘ S)))
  have : Smooth h := inferInstanceAs (Smooth (V.f b ≫ pullback.snd g i))
  let R := ProEtale.adicUpperStar l (pullback.fst p i)
  have hR : ∀ n : ℤ, ProEtale.IsAdicConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ n).obj (R.mapDerivedCategory.obj M)) := by
    intro n
    exact ProEtale.IsAdicConstructibleSheaf.of_iso
      ((R.mapDerivedCategoryHomologyFunctorIso n).app M)
      ((hc n).upperStar (pullback.fst p i))
  have hl := ProEtale.adicDerivedBaseChange_isIso_of_affine_of_smooth k₀ k l
    (IsPullback.of_hasPullback (pullback.snd p i) h) (R.mapDerivedCategory.obj M)
    (R.bounded_mapDerivedCategory_obj hM) hR
  obtain ⟨e⟩ := ProEtale.adicDerivedBaseChange_openChart l sq i j h w M
  exact (Arrow.isIso_iff_isIso_of_isIso e.hom).mpr hl

/-- **Geometric native smooth base change.** For a cartesian square
```
Z' --v--> Z
|p'       |p
v         v
T' --g--> T
```
of `k₀`-schemes with `g` smooth, `p` separated, quasi-compact and locally of finite type, and
`T`, `T'` locally of finite type over `k₀`, the native derived base-change morphism of the base
change of the square to the algebraic closure of `k₀` is invertible on bounded complexes with
constructible cohomology. -/
theorem geometric_smooth_baseChange_isIso [Fact (ringChar k₀ ≠ l)]
    (sq : IsPullback v p' p g) [Smooth g] [IsSeparated p] [QuasiCompact p]
    [LocallyOfFiniteType p]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T' ↘ Spec (CommRingCat.of k₀))]
    (M : _root_.DerivedCategory
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (hM : _root_.DerivedCategory.TStructure.t.bounded M)
    (hc : ∀ n : ℤ, ProEtale.IsAdicConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ n).obj M)) :
    IsIso ((ProEtale.adicDerivedBaseChange l (geometricSquare k₀ sq.toCommSq)).app M) := by
  let S := Spec (CommRingCat.of (AlgebraicClosure k₀))
  let : (T ↘ Spec (CommRingCat.of k₀)).geometricFiber.Over S :=
    ⟨(T ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure⟩
  let : (T' ↘ Spec (CommRingCat.of k₀)).geometricFiber.Over S :=
    ⟨(T' ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure⟩
  have : LocallyOfFiniteType ((T ↘ Spec (CommRingCat.of k₀)).geometricFiber ↘ S) :=
    inferInstanceAs (LocallyOfFiniteType
      (T ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)
  have : LocallyOfFiniteType ((T' ↘ Spec (CommRingCat.of k₀)).geometricFiber ↘ S) :=
    inferInstanceAs (LocallyOfFiniteType
      (T' ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)
  have : (geometricMap k₀ g).IsOver S :=
    ⟨Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure _ _⟩
  have : Smooth (geometricMap k₀ g) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Smooth) g
      (comp_over g (Spec (CommRingCat.of k₀))) inferInstance
  have : IsSeparated (geometricMap k₀ p) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsSeparated) p
      (comp_over p (Spec (CommRingCat.of k₀))) inferInstance
  have : QuasiCompact (geometricMap k₀ p) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @QuasiCompact) p
      (comp_over p (Spec (CommRingCat.of k₀))) inferInstance
  have : LocallyOfFiniteType (geometricMap k₀ p) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @LocallyOfFiniteType) p
      (comp_over p (Spec (CommRingCat.of k₀))) inferInstance
  exact affineChart_descent_of_smooth k₀ l (AlgebraicClosure k₀)
    (isPullback_geometricSquare k₀ sq) M hM hc

end NativeBaseChange

end AlgebraicGeometry
