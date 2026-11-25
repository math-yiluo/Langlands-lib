/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism.PointClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStarShift
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The trace isomorphism

Let `k` be an algebraically closed field, `Λ` a finite coefficient ring whose exponent is
invertible in `k` (the finite stage `A_{E,n}` of the blueprint), and `a : X ⟶ Spec k` smooth,
proper and geometrically connected of pure relative dimension `d`, with a Tate orientation
`γ : Λ_X(d)[2d] ≅ Ra^! Λ`. The trace isomorphism says:

* the untwisted trace `tr^{(-d)}_X : H^{2d}(X, Λ) ⟶ Λ(-d)` is bijective, whatever the
  orientation `γ`;
* for the normalized orientation, its twist `tr_X : H^{2d}(X, Λ(d)) ⟶ Λ` sends the class
  `[x ⊂ X]` of every `k`-point `x` of `X` to `1`.

The class `[x ⊂ X]` is the image in `H^{2d}(X, Λ(d)) = H^{2d}_c(X, Λ(d))` of the fundamental
class of the regular closed immersion `x : Spec k ⟶ X` of codimension `d`
(`AlgebraicGeometry.Etale.fundamentalClass`, `lemma-class-of-point--1`), obtained by forgetting
supports.

## Main definitions

- `AlgebraicGeometry.Etale.unitClassCompactSupport`: the class `1 ∈ H^0_c(X, Λ)`.
- `AlgebraicGeometry.Etale.TateOrientation.traceDualityEquiv`: the duality at `i = 0`,
  `H^{2d}_c(X, Λ(d)) ≃ Hom(Ra_! Λ_X, Λ_Y)`.
- `AlgebraicGeometry.Etale.pointClass`: the class `[x ⊂ X] ∈ H^{2d}_c(X, Λ(d))` of a `k`-point.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.traceMap_eq_unitClassCompactSupport_comp`: the trace
  `tr_X : H^{2d}_c(X, Λ(d)) ⟶ Λ` is the map produced by the duality at `i = 0`, followed by
  evaluation at `1 ∈ H^0_c(X, Λ)`; `bijective_traceMap_iff` is the resulting criterion.
- `AlgebraicGeometry.Etale.TateOrientation.bijective_untwistedTraceMap`: the untwisted trace
  `H^{2d}_c(X, Λ) ⟶ Λ(-d)` is bijective.
- `AlgebraicGeometry.Etale.exists_tateOrientation_traceMap_pointClass`: for a suitable (the
  normalized) orientation the trace sends every point class to `1`. It rests on
  `AlgebraicGeometry.Etale.pointClass_eq` (all `k`-points have the same class) and
  `AlgebraicGeometry.Etale.isIso_traceMap_pointClass` (the trace of a point class is invertible).
- `AlgebraicGeometry.Etale.traceIsomorphism` (`corollary-cup-product-pairing--1`): the trace
isomorphism
  `H^{2d}(X, Λ) ≅ Λ(-d)` and the normalization of the trace by point classes.

## Implementation notes

*The normalized orientation.* The repository has smooth purity only as the existence of an
isomorphism `Λ_X(d)[2d] ≅ Ra^! Λ`
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`), not the canonical
orientation built from Kummer classes in `proposition-smooth-purity-finite-coefficients`. The
normalization is therefore stated as the existence of a Tate orientation whose trace sends all point
classes to `1`.

*Points.* A `k`-point `x` of the smooth `X` is a regular closed immersion of codimension `d`; this
is taken as an instance argument `[IsRegularImmersion d x]`.

*Other coefficient stages.* The stages `𝒪_E`, `E` and `ℚ̄_ℓ` are not available for the étale
derived categories of the repository (see
`WeilConjectures.EtaleCohomology.PoincareDuality.Transport`). The field-stage statements with
their Frobenius actions are in `WeilConjectures.WeilSheaf.TraceIsomorphism`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section DualityAtZero

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y} [HasCompactification a] [IsProper a] {d : ℕ}

variable (Λ a) in
/-- The class `1 ∈ H^0_c(X, Λ)` of a proper morphism `a : X ⟶ Y`, as a morphism
`Λ_Y ⟶ Ra_! Λ_X`: the unit `Λ_Y ⟶ Ra_* La^* Λ_Y` of `La^* ⊣ Ra_*`, read through
`La^* Λ_Y ≅ Λ_X` and `Ra_* ≅ Ra_!`. -/
noncomputable def unitClassCompactSupport :
    𝟙_ (DerivedCategoryModule Λ Y) ⟶ (R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X) :=
  (derivedUpperStarLowerStarAdjunction _ a).unit.app (constantComplex Λ Y) ≫
    (R((a)_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ a).hom ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).inv.app _

namespace TateOrientation

/-- Blueprint `corollary-cup-product-pairing--1` (the duality at `i = 0`): for a Tate orientation
`γ` of a proper morphism `a : X ⟶ Y`, the duality isomorphism in degree `0`,
`H^{2d}_c(X, Λ(d)) ≃ Hom(Ra_! Λ_X, Λ_Y)`, that is `H^{2d}(X, Λ(d)) ≅ H^0_c(X, Λ)^∨` over a
separably closed field. It is the composite
```
Hom(Λ_Y, (Ra_! Λ_X(d))[2d]) ≃ Hom(Λ_Y, Ra_*(Λ_X(d)[2d]))      (Ra_! ≅ Ra_*)
                            ≃ Hom(Λ_X, Λ_X(d)[2d])            (La^* ⊣ Ra_*, La^* Λ_Y ≅ Λ_X)
                            ≃ Hom(Λ_X, Ra^! Λ_Y)              (γ)
                            ≃ Hom(Ra_! Λ_X, Λ_Y)              (Ra_! ⊣ Ra^!).
``` -/
noncomputable def traceDualityEquiv (γ : TateOrientation Λ a d) :
    ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj (tateObject Λ X d))⟦(2 * d : ℤ)⟧) ≃
      ((R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X) ⟶
        𝟙_ (DerivedCategoryModule Λ Y)) :=
  (((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).symm.app _ ≪≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).app _).homToEquiv.trans <|
    ((derivedUpperStarLowerStarAdjunction _ a).homEquiv _ _).symm.trans <|
      ((leftDerivedUpperStarConstantComplexIso Λ a).homCongr γ.dualizingComplexIso).trans
        ((rightDerivedUpperShriekAdjunction _ a).homEquiv _ _).symm

/-- Blueprint `corollary-cup-product-pairing--1` (the trace is the map produced by the duality at
`i = 0`): the trace map `tr_X : H^{2d}_c(X, Λ(d)) ⟶ Λ` of a Tate orientation `γ` of a proper
morphism `a` is the duality isomorphism `H^{2d}_c(X, Λ(d)) ≃ Hom(Ra_! Λ_X, Λ_Y)`
(`AlgebraicGeometry.Etale.TateOrientation.traceDualityEquiv`) followed by evaluation at the
class `1 ∈ H^0_c(X, Λ)` (`AlgebraicGeometry.Etale.unitClassCompactSupport`). -/
theorem traceMap_eq_unitClassCompactSupport_comp (γ : TateOrientation Λ a d)
    (c : (𝟙_ (DerivedCategoryModule Λ Y)) ⟶
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj (tateObject Λ X d))⟦(2 * d : ℤ)⟧) :
    γ.traceMap c = unitClassCompactSupport Λ a ≫ γ.traceDualityEquiv c :=
  Adjunction.comp_map_counit_eq_comp_homEquiv_symm (derivedUpperStarLowerStarAdjunction _ a)
    (rightDerivedUpperShriekAdjunction _ a) (rightDerivedLowerShriekIsoRightDerivedLowerStar _ a)
    (A := constantComplex Λ Y) (leftDerivedUpperStarConstantComplexIso Λ a)
    (((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).symm.app _)
    γ.dualizingComplexIso c

/-- The trace map `tr_X : H^{2d}_c(X, Λ(d)) ⟶ Λ` of a Tate orientation of a proper morphism is
bijective if and only if evaluation at `1 ∈ H^0_c(X, Λ)`,
`Hom(Ra_! Λ_X, Λ_Y) ⟶ Hom(Λ_Y, Λ_Y)`, is bijective, that is if and only if
`H^0_c(X, Λ)^∨ ⟶ Λ` is: the trace is this evaluation read through the duality at `i = 0`
(`AlgebraicGeometry.Etale.TateOrientation.traceMap_eq_unitClassCompactSupport_comp`). -/
theorem bijective_traceMap_iff (γ : TateOrientation Λ a d) :
    Function.Bijective γ.traceMap ↔ Function.Bijective
      (fun h : (R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X) ⟶
        𝟙_ (DerivedCategoryModule Λ Y) ↦ unitClassCompactSupport Λ a ≫ h) := by
  have : ⇑γ.traceMap = (fun h ↦ unitClassCompactSupport Λ a ≫ h) ∘ γ.traceDualityEquiv :=
    funext (traceMap_eq_unitClassCompactSupport_comp γ)
  rw [this]
  exact Function.Bijective.of_comp_iff _ γ.traceDualityEquiv.bijective

end TateOrientation

end DualityAtZero

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} [HasInvertibleExponent Λ X] {d : ℕ}
  (a : X ⟶ Spec (.of k)) [IsProper a] [SmoothOfRelativeDimension d a] [GeometricallyConnected a]

namespace TateOrientation

variable [HasTateTwist Λ]

omit [HasInvertibleExponent Λ (Spec (.of k))] [HasInvertibleExponent Λ X]
  [SmoothOfRelativeDimension d a] in
/-- Blueprint `corollary-cup-product-pairing--1` (the trace isomorphism, twisted form): for `X`
proper and geometrically connected over the algebraically closed field `k`, a self-injective finite
coefficient ring `Λ` and any Tate orientation `γ`, the trace map
`tr_X : H^{2d}_c(X, Λ(d)) ⟶ Λ` is bijective. Through the duality at `i = 0` it is evaluation at
`1 ∈ H^0_c(X, Λ)`, `Hom(Ra_! Λ_X, Λ) ⟶ Hom(Λ, Λ)`
(`AlgebraicGeometry.Etale.TateOrientation.bijective_traceMap_iff`), which is bijective as
`H^0(X, Λ) = Λ` for the connected `X` and `Λ` is self-injective
(`AlgebraicGeometry.Etale.bijective_comp_unit_rightDerivedLowerStar`). -/
theorem bijective_traceMap [Module.Injective Λ Λ] (γ : TateOrientation Λ a d) :
    Function.Bijective γ.traceMap := by
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton (f := a)
  rw [bijective_traceMap_iff]
  have h := bijective_comp_unit_rightDerivedLowerStar (Λ := Λ) a
    (leftDerivedUpperStarConstantComplexIso Λ a)
  let α := (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a).app
    (constantComplex Λ X)
  let v := (derivedUpperStarLowerStarAdjunction _ a).unit.app (𝟙_ _) ≫
    (R((a)_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ a).hom
  have hu : unitClassCompactSupport Λ a = v ≫ α.inv := by
    rw [Category.assoc]
    rfl
  rw [hu]
  refine ⟨fun h₁ h₂ h₁₂ ↦ ?_, fun z ↦ ?_⟩
  · replace h₁₂ : v ≫ α.inv ≫ h₁ = v ≫ α.inv ≫ h₂ := by
      simpa only [Category.assoc] using h₁₂
    simpa only [Iso.hom_inv_id_assoc] using α.hom ≫= h.1 h₁₂
  · obtain ⟨g, hg⟩ := h.2 z
    refine ⟨α.hom ≫ g, ?_⟩
    replace hg : v ≫ g = z := hg
    change (v ≫ α.inv) ≫ α.hom ≫ g = z
    rw [Category.assoc, Iso.inv_hom_id_assoc, hg]

omit [SmoothOfRelativeDimension d a] in
/-- Blueprint `corollary-cup-product-pairing--1` (the trace isomorphism, compactly supported form):
for `X` smooth, proper and geometrically connected of pure dimension `d` over the algebraically
closed field `k`, a self-injective finite coefficient ring `Λ` (such as `A_{E,n} = 𝒪_E/ϖⁿ`) and any
Tate orientation `γ`, the untwisted trace map `tr^{(-d)}_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)` is bijective:
the twisted trace is (`AlgebraicGeometry.Etale.TateOrientation.bijective_traceMap`), and over
the algebraically closed `k` the Tate twists are trivial
(`AlgebraicGeometry.Etale.TateOrientation.bijective_untwistedTraceMap_of_bijective_traceMap`). -/
theorem bijective_untwistedTraceMap [Module.Injective Λ Λ] (γ : TateOrientation Λ a d) :
    Function.Bijective γ.untwistedTraceMap :=
  bijective_untwistedTraceMap_of_bijective_traceMap γ (bijective_traceMap a γ)

omit [SmoothOfRelativeDimension d a] in
/-- The untwisted trace on ordinary cohomology, `tr^{(-d)}_X : H^{2d}(X, Λ) ⟶ Λ(-d)`, is
bijective: it is `AlgebraicGeometry.Etale.TateOrientation.untwistedTraceMap` read through
`H^{2d}(X, Λ) ≃ H^{2d}_c(X, Λ)`. -/
theorem bijective_untwistedTraceMap_comp_cohomologyAddEquivCompactSupport
    [Module.Injective Λ Λ] (γ : TateOrientation Λ a d) :
    Function.Bijective (γ.untwistedTraceMap.comp (cohomologyAddEquivCompactSupport a
      (leftDerivedUpperStarConstantComplexIso Λ a) (2 * d)).toAddMonoidHom) :=
  (bijective_untwistedTraceMap a γ).comp (AddEquiv.bijective _)

end TateOrientation

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]

/-- The class `[x ⊂ X] ∈ H^{2d}_c(X, Λ(d))` of a `k`-point `x : Spec k ⟶ X`: the fundamental
class `[x ⊂ X] ∈ H^{2d}_x(X, Λ(d))` of the regular closed immersion `x` of codimension `d`
(`AlgebraicGeometry.Etale.fundamentalClass`), mapped to `H^{2d}(X, Λ(d))` by forgetting supports,
that is by the counit `Rx_! Rx^! ⟶ 𝟙` of `Rx_! ⊣ Rx^!`, and read in `H^{2d}_c(X, Λ(d))` through
the adjunction `La^* ⊣ Ra_*` and `Ra_* ≅ Ra_!`. -/
noncomputable def pointClass (x : Spec (.of k) ⟶ X) [IsRegularImmersion d x] :
    𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶
      ((R(a)_![ModuleCat.{u + 1} Λ]).obj (tateObject Λ X d))⟦(2 * d : ℤ)⟧ :=
  haveI := HasInvertibleExponent.of_hom (Λ := Λ) a
  haveI := SmoothOfRelativeDimension.smooth d a
  (derivedUpperStarLowerStarAdjunction _ a).homEquiv _ _
      ((leftDerivedUpperStarConstantComplexIso Λ a).hom ≫
        fundamentalClass Λ d x a IsRegular.isRegularLocalRing_stalk ≫
          (rightDerivedUpperShriekAdjunction _ x).counit.app _) ≫
    (rightDerivedLowerStarShiftIsoLowerShriek a (tateObject Λ X d) (2 * d)).hom

omit [HasInvertibleExponent Λ X] [GeometricallyConnected a] [HasKummerClass.IsNormalized Λ] in
/-- The class of a `k`-point does not depend on the point: the fundamental classes of any two
`k`-points agree once their supports are forgotten
(`AlgebraicGeometry.Etale.fundamentalClass_comp_counit_eq_of_section`). -/
theorem pointClass_eq [HasKummerClass.IsNormalized Λ] [Module.Injective Λ Λ] [ConnectedSpace X]
    (x y : Spec (.of k) ⟶ X) [IsRegularImmersion d x] [IsRegularImmersion d y]
    (hx : x ≫ a = 𝟙 _) (hy : y ≫ a = 𝟙 _) :
    pointClass (Λ := Λ) (d := d) a x = pointClass (Λ := Λ) (d := d) a y := by
  have := HasInvertibleExponent.of_hom (Λ := Λ) a
  simp only [pointClass]
  rw [fundamentalClass_comp_counit_eq_of_section Λ a x y hx hy]

omit [Finite Λ] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  [HasInvertibleExponent Λ X]
  [GeometricallyConnected a] [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] in
/-- The shift isomorphisms of `Ra_*` and `Ra_!` combine into the identification `Ra_* ≅ Ra_!`
at a shifted object. -/
lemma rightDerivedLowerStarShiftIsoLowerShriek_hom_comp_commShiftIso_inv
    (M : DerivedCategoryModule Λ X) (n : ℤ) :
    (rightDerivedLowerStarShiftIsoLowerShriek a M n).hom ≫
        ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso n).inv.app M =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a).inv.app (M⟦n⟧) := by
  have := NatTrans.shift_app_comm
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a).inv n M
  simp only [rightDerivedLowerStarShiftIsoLowerShriek, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [reassoc_of% this, Iso.hom_inv_id_app]
  erw [Category.comp_id]
omit [HasInvertibleExponent Λ (Spec (.of k))] [GeometricallyConnected a] in
omit [GeometricallyConnected a] in
/-- The trace of the class of a `k`-point is invertible, in a form with an arbitrary unit
object `U` and identification `e : La^* U ≅ Λ_X`: up to isomorphisms it is the unit of
`La^* ⋙ Lx^* ⊣ Rx_* ⋙ Ra_*` (whose left adjoint is `L(x ≫ a)^* = 𝟭`), followed by the
fundamental class `cl_x : Λ ≅ Rx^! Λ_X(d)[2d]` of `x`
(`AlgebraicGeometry.Etale.isIso_fundamentalClassMap`), the orientation and the counit of
`Rx_! ⋙ Ra_! ⊣ Ra^! ⋙ Rx^!` (whose left adjoint is `Rx_* ⋙ Ra_* ≅ 𝟭`). -/
theorem isIso_homEquiv_fundamentalClass_comp_smoothTrace (γ : TateOrientation Λ a d)
    (x : Spec (.of k) ⟶ X) [IsRegularImmersion d x] (hx : x ≫ a = 𝟙 _)
    {U : DerivedCategoryModule Λ (Spec (.of k))}
    (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj U ≅ constantComplex Λ X) :
    haveI := SmoothOfRelativeDimension.smooth d a
    IsIso (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).homEquiv U _
        (e.hom ≫ fundamentalClass Λ d x a IsRegular.isRegularLocalRing_stalk ≫
          (rightDerivedUpperShriekAdjunction _ x).counit.app _) ≫
        (rightDerivedLowerStarShiftIsoLowerShriek a (tateObject Λ X d) (2 * d)).hom) ≫
      ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ.smoothTrace) := by
  have := SmoothOfRelativeDimension.smooth d a
  have hB := isIso_unit_comp_map_of_isIso_supportedClassMap a x hx e
    (fundamentalClass Λ d x a IsRegular.isRegularLocalRing_stalk)
    (isIso_fundamentalClassMap Λ d x a _)
  let adjS := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) x)
  let ψ := (adjS.ofNatIsoLeft (leftDerivedUpperStarCompSectionIso _ x a hx)).rightAdjointUniq
    Adjunction.id
  let adjB := (rightDerivedUpperShriekAdjunction Λ x).comp
    (rightDerivedUpperShriekAdjunction Λ a)
  have hC : IsIso adjB.counit := adjB.isIso_counit_of_iso_id
    (Functor.isoWhiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar _ x) _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerShriekIsoRightDerivedLowerStar _ a) ≪≫ ψ)
  have key : (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).homEquiv U _
        (e.hom ≫ fundamentalClass Λ d x a IsRegular.isRegularLocalRing_stalk ≫
          (rightDerivedUpperShriekAdjunction _ x).counit.app _) ≫
        (rightDerivedLowerStarShiftIsoLowerShriek a (tateObject Λ X d) (2 * d)).hom) ≫
      ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ.smoothTrace) =
      ((derivedUpperStarLowerStarAdjunction _ a).unit.app U ≫
        (R((a)_*[ModuleCat.{u + 1} Λ])).map (e.hom ≫
          fundamentalClass Λ d x a IsRegular.isRegularLocalRing_stalk)) ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a).inv.app _ ≫
        ((R(a)_![ModuleCat.{u + 1} Λ]).map ((rightDerivedUpperShriekAdjunction _ x).counit.app
          ((tateObject Λ X d)⟦(2 * d : ℤ)⟧)) ≫ γ.smoothTrace) := by
    rw [Category.assoc,
      reassoc_of% rightDerivedLowerStarShiftIsoLowerShriek_hom_comp_commShiftIso_inv,
      Adjunction.homEquiv_unit]
    dsimp only [Functor.id_obj, Functor.comp_obj]
    simp only [Functor.map_comp, Category.assoc]
    rw [(rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ)
      a).inv.naturality_assoc]
  have hT : IsIso ((R(a)_![ModuleCat.{u + 1} Λ]).map
      ((rightDerivedUpperShriekAdjunction _ x).counit.app ((tateObject Λ X d)⟦(2 * d : ℤ)⟧)) ≫
        γ.smoothTrace) := by
    unfold TateOrientation.smoothTrace Etale.smoothTrace
    exact Adjunction.isIso_map_counit_app_comp_map_comp_counit_app
      (rightDerivedUpperShriekAdjunction Λ x)
      (rightDerivedUpperShriekAdjunction Λ a) hC _ _
  rw [key]
  infer_instance

omit [GeometricallyConnected a] in
/-- The trace of the class of a `k`-point is invertible, for every Tate orientation
(`AlgebraicGeometry.Etale.isIso_homEquiv_fundamentalClass_comp_smoothTrace`). -/
theorem isIso_traceMap_pointClass (γ : TateOrientation Λ a d) (x : Spec (.of k) ⟶ X)
    [IsRegularImmersion d x] (hx : x ≫ a = 𝟙 _) : IsIso (γ.traceMap (pointClass a x)) :=
  isIso_homEquiv_fundamentalClass_comp_smoothTrace a γ x hx
    (leftDerivedUpperStarConstantComplexIso Λ a)

omit [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))] [HasInvertibleExponent Λ X]
  [SmoothOfRelativeDimension d a] [GeometricallyConnected a] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] in
/-- Rescaling a Tate orientation `γ` by an automorphism `φ` of `Λ_k` rescales its trace by
`φ`, by naturality of the counit of `Ra_! ⊣ Ra^!`. -/
lemma TateOrientation.traceMap_trans_mapIso [HasTateTwist Λ] (γ : TateOrientation Λ a d)
    (φ : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ≅ 𝟙_ _)
    (c : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶
      ((R(a)_![ModuleCat.{u + 1} Λ]).obj (tateObject Λ X d))⟦(2 * d : ℤ)⟧) :
    TateOrientation.traceMap (γ ≪≫ (R(a)^![Λ]).mapIso φ) c =
      γ.traceMap c ≫ φ.hom := by
  have e (γ' : TateOrientation Λ a d) : γ'.traceMap c = c ≫
      ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ'.smoothTrace := rfl
  rw [e, e]
  simp only [TateOrientation.smoothTrace, Etale.smoothTrace, TateOrientation.dualizingComplexIso,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [(rightDerivedUpperShriekAdjunction _ a).counit_naturality]

/-- Blueprint `corollary-cup-product-pairing--1` (normalization of the trace by points): there is a
Tate orientation `γ` of `a` — the normalized orientation of
`proposition-smooth-purity-finite-coefficients` — whose trace map `tr_X : H^{2d}_c(X, Λ(d)) ⟶ Λ`
sends the class `[x ⊂ X]` of every `k`-point `x` to `1`.

This is not an independent convention. The blueprint derives it from `lemma-class-of-point--1` (c)
and the compatibility of smooth purity with composition. The repository has smooth purity only as
the existence of an orientation, and the proof is the following equivalent argument:
* all `k`-points have the same class (`AlgebraicGeometry.Etale.pointClass_eq`): the point `y` is
  the base change of the diagonal along `X ≅ X × {y} ⊆ X × X`, and by proper base change the
  restriction to `X × {y}` does not depend on `y`, as `H^0(X, Λ) = Λ` for the connected `X`;
* for any orientation the trace of a point class is invertible
  (`AlgebraicGeometry.Etale.isIso_traceMap_pointClass`), so rescaling the orientation by its
  inverse (`AlgebraicGeometry.Etale.TateOrientation.traceMap_trans_mapIso`) normalizes it.

The coefficient ring is assumed self-injective, as the finite stages `A_{E,n} = 𝒪_E/ϖⁿ` of the
blueprint are: this is what makes the restriction `Ra_* Λ_X ⟶ Λ` to a point independent of the
point. -/
theorem exists_tateOrientation_traceMap_pointClass [Module.Injective Λ Λ] :
    ∃ γ : TateOrientation Λ a d, ∀ (x : Spec (.of k) ⟶ X) [IsRegularImmersion d x],
      x ≫ a = 𝟙 _ → γ.traceMap (pointClass a x) = 𝟙 _ := by
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton (f := a)
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := d) a (𝟙 _)
  by_cases h : ∃ (x : Spec (.of k) ⟶ X) (_ : IsRegularImmersion d x), x ≫ a = 𝟙 _
  · obtain ⟨x₀, _, hx₀⟩ := h
    have := isIso_traceMap_pointClass a θ.symm x₀ hx₀
    refine ⟨θ.symm ≪≫ (R(a)^![Λ]).mapIso
      (asIso (TateOrientation.traceMap θ.symm (pointClass a x₀))).symm,
      fun x _ hx ↦ ?_⟩
    rw [TateOrientation.traceMap_trans_mapIso, pointClass_eq a x x₀ hx hx₀]
    simp
  · exact ⟨θ.symm, fun x _ hx ↦ (h ⟨x, ‹_›, hx⟩).elim⟩

/-- Blueprint `corollary-cup-product-pairing--1`: The trace isomorphism.

Let `X` be smooth, proper and geometrically connected of pure dimension `d` over the
algebraically closed field `k`, and let `Λ` be a self-injective finite coefficient ring whose
exponent is invertible in `k` (such as `A_{E,n} = 𝒪_E/ϖⁿ`). Then:

1. for every Tate orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ`, the untwisted trace
   `tr^{(-d)}_X : H^{2d}(X, Λ) ⟶ Λ(-d)` is an isomorphism;
2. for the normalized orientation, the twisted trace `tr_X : H^{2d}(X, Λ(d)) ⟶ Λ` sends the
   class `[x ⊂ X]` of every `k`-point `x ∈ X(k)` to `1`.

See the module docstring for the form of the normalization. -/
theorem traceIsomorphism [Module.Injective Λ Λ] :
    (∀ γ : TateOrientation Λ a d,
      Function.Bijective (γ.untwistedTraceMap.comp (cohomologyAddEquivCompactSupport a
        (leftDerivedUpperStarConstantComplexIso Λ a) (2 * d)).toAddMonoidHom)) ∧
    ∃ γ : TateOrientation Λ a d, ∀ (x : Spec (.of k) ⟶ X) [IsRegularImmersion d x],
      x ≫ a = 𝟙 _ → γ.traceMap (pointClass a x) = 𝟙 _ :=
  ⟨TateOrientation.bijective_untwistedTraceMap_comp_cohomologyAddEquivCompactSupport a,
    exists_tateOrientation_traceMap_pointClass a⟩

end Etale

end AlgebraicGeometry
