/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.FiniteTorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Fixed.FixedExponentDerivedCoproducts
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorDirectSums
import WeilConjectures.SixFunctors.Etale.Derived.ConstantTensorProjection
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration

/-!
# Constant-module projection for bounded torsion objects

Source: Stacks Project, Tag 0F12, `lemma-pull-out-constant-mod-n`, relative fixed-exponent
extension; and the docstring of `torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing`
in `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage`
(blueprint: lem-sf-projection-torsion-object-constant).

The map is the existing counit mate, a natural transformation of bifunctors. Its target
is identified with `Rf_*(E ⊗ᴸ M_X[0])` by the canonical constant inverse-image isomorphism.
The statement concerns the uncompleted tensor in the ordinary unbounded derived category.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The constant-module projection map is invertible for a bounded torsion object of finite
Tor amplitude over Noetherian coefficients. There is no finiteness or flatness condition
on the module and no constructibility condition on the object. Naturality in both variables
is that of `rightDerivedLowerStarProjectionMap`, restricted along the constant-sheaf functor
and the degree-zero embedding. The canonical constant inverse-image comparison identifies
its target with `Rf_*(E ⊗ᴸ M_X[0])`, naturally in `M`.

Source: Stacks Project, Tag 0F12, `lemma-pull-out-constant-mod-n`, direct-sum/triangle/unit
argument adapted to relative direct image and a fixed-exponent torsion object; the docstring
of `torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing` in the direct-image stability
module (blueprint: lem-sf-projection-torsion-object-constant).

Proof:
1. Finite-type schemes over a field are Noetherian and the source is quasi-compact.
   Tag 0F10(1) gives finite relative torsion cohomological dimension for `f`.
2. Restrict the existing projection natural transformation along the exact termwise
   derived constant-sheaf functor `C`. Its source and target are triangulated and it
   commutes with shifts, by the existing etale shift and triangulated-functor instances.
   The existing projection-unit theorem, the monoidal constant-sheaf unit comparison,
   and `mapDerivedCategorySingleFunctor` give its invertibility at `Λ[0]`.
3. For every `P`, the additive functor `(- ⊗ᴸ P)` sends `N • id_E = 0` to
   `N • id_(E ⊗ᴸ P) = 0`. Apply the fixed-exponent coproduct theorem to the family
   `E ⊗ᴸ Lf^* C(P_i)`. Its invertible canonical coproduct comparison proves preservation
   of this particular coproduct by `Rf_*`. Constants, inverse image, and tensor preserve
   all coproducts, so both functors in the restricted transformation preserve coproducts.
4. The isomorphism locus contains shifts of the rank-one free module, including the
   harmless `ULift` used by `derivedModuleFreeGeneration`. It is closed under coproducts
   by naturality and preservation, under third vertices of distinguished triangles by
   the triangle-isomorphism theorem, and under retracts by naturality. Free generation
   therefore gives invertibility at every object of `D(Λ)`.
5. Evaluate at `M[0]` and transport along `mapDerivedCategorySingleFunctor`, obtaining
   exactly the displayed component of the original projection transformation. The result
   does not require changing coefficients or identifying a different projection map.
-/
theorem isIso_rightDerivedLowerStarProjectionMap_constant_of_torsion_object
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsSeparated f]
    (E : DerivedCategoryModule Λ X)
    (N : ℕ) (hNpos : 1 ≤ N) (hN : N • 𝟙 E = 0) (M : ModuleCat.{u + 1} Λ) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have hcd := (torsionEtaleCohomologicalDimension_finite_of_finiteType k X Y f).1
  let A := ModuleCat.{u + 1} Λ
  let C := constantFunctor Λ Y
  let L : DerivedCategoryModule Λ Y ⥤ DerivedCategoryModule Λ X := L((f)^*[A])
  let R : DerivedCategoryModule Λ X ⥤ DerivedCategoryModule Λ Y :=
    rightDerivedLowerStar A f
  let T := (derivedTensor A X).obj E
  let H := C ⋙ L ⋙ T
  let τ := Functor.whiskerLeft C (rightDerivedLowerStarProjectionMapApp Λ f E)
  have hT : ∀ P, N • 𝟙 (T.obj P) = 0 := by
    intro P
    let B := (derivedTensor A X).flip.obj P
    have hh := congrArg B.map hN
    have hid : B.map (𝟙 E) = 𝟙 (T.obj P) := B.map_id E
    rwa [Functor.map_nsmul, hid, Functor.map_zero] at hh
  have hR (I : Type (u + 1)) (P : I → _root_.DerivedCategory A) :
      PreservesColimit (Discrete.functor P ⋙ H) R := by
    let K := fun i ↦ H.obj (P i)
    let := derived_hasCoproducts
      (C := Sheaf X.smallEtaleTopology A) I
    let := derived_hasCoproducts
      (C := Sheaf Y.smallEtaleTopology A) I
    have : IsIso (sigmaComparison R K) :=
      isIso_sigmaComparison_rightDerivedLowerStar_of_fixedExponent Λ f hcd N hNpos I K
        (fun i ↦ hT _)
    have : PreservesColimit (Discrete.functor K) R :=
      PreservesCoproduct.of_iso_comparison R K
    exact preservesColimit_of_iso_diagram R
      (show Discrete.functor K ≅ Discrete.functor P ⋙ H from
        Discrete.natIso (fun _ ↦ Iso.refl _))
  have hL (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) L :=
    (derivedUpperStarLowerStarAdjunction A f).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have hH (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) H := by
    have := hL I
    have := (derivedTensor_preservesDirectSums Λ X E).1 I
    dsimp only [H, T, C]
    infer_instance
  have hsource (I : Type (u + 1)) :
      PreservesColimitsOfShape (Discrete I) (C ⋙ (derivedTensor A Y).obj (R.obj E)) := by
    have := (derivedTensor_preservesDirectSums Λ Y (R.obj E)).1 I
    dsimp only [C]
    infer_instance
  have htarget (I : Type (u + 1)) (P : I → _root_.DerivedCategory A) :
      PreservesColimit (Discrete.functor P) (H ⋙ R) := by
    have := hR I P
    have := hH I
    change PreservesColimit (Discrete.functor P) (H ⋙ R)
    infer_instance
  have hu : IsIso (τ.app
      ((_root_.DerivedCategory.singleFunctor A 0).obj (ModuleCat.of Λ Λ))) := by
    change IsIso ((rightDerivedLowerStarProjectionMapApp Λ f E).app _)
    exact isIso_rightDerivedLowerStarProjectionMapApp_of_iso
      ((Functor.mapDerivedCategorySingleFunctor _ 0).app (ModuleCat.of Λ Λ)).symm
      (isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_self Λ f E)
  have hτ (P : _root_.DerivedCategory A) : IsIso (τ.app P) := by
    apply derivedModuleFreeGeneration.{u + 1, 0} Λ P (fun P ↦ IsIso (τ.app P))
    · intro n
      apply (NatTrans.isIso_app_shift_iff τ _ n).2
      exact (NatTrans.isIso_app_iff_of_iso τ
        ((_root_.DerivedCategory.singleFunctor A 0).mapIso
          (ULift.moduleEquiv : ULift.{0} Λ ≃ₗ[Λ] Λ).toModuleIso)).2 hu
    · intro I P S ι hc hP
      have := hsource I
      have := htarget I P
      exact NatTrans.isIso_app_of_isColimit_cofan
        (F := C ⋙ (derivedTensor A Y).obj (R.obj E)) (G := H ⋙ R) τ hc hP
    · intro T hT h₁ h₂
      exact NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂ τ hT h₁ h₂
    · intro P Q h hQ
      have := hQ
      exact NatTrans.isIso_app_of_retract τ h
  exact isIso_rightDerivedLowerStarProjectionMapApp_of_iso
    ((Functor.mapDerivedCategorySingleFunctor _ 0).app M)
    (hτ ((_root_.DerivedCategory.singleFunctor A 0).obj M))

end AlgebraicGeometry.Etale
