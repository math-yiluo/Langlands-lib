/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsSequentialColimit
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapMulLeft
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralDenominators
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarMapEq
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationOfModels

/-!

# Bounded constructible `E`-coefficients as `𝒪_E`-coefficients with `ℓ` inverted

Let `X` be a scheme, `ℓ` a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`) with ring of integers `𝒪_E`. The condensed rings
`𝒪̲_E = Profinite.padicIntegersRingObj ℓ E` and `E̲ = Profinite.continuousMapRingObj E`, for the
norm of `E` restricted from `ℚ̄_ℓ`, pull back along `p_X : X_proét ⟶ *_proét` to the
coefficient ring objects `𝒪_{E,X} = p_X^* 𝒪̲_E` and `E_X = p_X^* E̲` of abelian pro-étale sheaves
on `X` (`ProEtale.condensedRingObj`), and the pullback of the inclusion `𝒪̲_E ⟶ E̲`
(`ProEtale.padicIntegersRingObjToContinuousMapRingObj`) is a morphism of ring objects
`φ : 𝒪_{E,X} ⟶ E_X` (`ProEtale.padicIntegersToPadicSubfield`).

The derived extension of scalars
```
E ⊗ᴸ_{𝒪_E} - = L(extendScalars φ) : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})
```
of `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` preserves bounded
constructible complexes (`ProEtale.boundedConstructible_derivedExtendScalars_obj`), so it
restricts to a functor
`D_cons(X_proét, 𝒪_E) ⥤ D_cons(X_proét, E)` (`ProEtale.boundedConstructibleExtendScalars`) on
the bounded constructible derived categories `ProEtale.BoundedConstructible` of
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.

For `X` topologically noetherian, this file states that the restricted functor exhibits
`D_cons(X_proét, E)` as `D_cons(X_proét, 𝒪_E)` with `ℓ` inverted: it is a localization functor
with respect to the class
`CategoryTheory.Rationalization.W (Submonoid.powers ℓ) D_cons(X_proét, 𝒪_E)` of morphisms whose
mapping cone is killed by some power `ℓⁿ`
(`ProEtale.isLocalization_boundedConstructibleExtendScalars`). Consequently
`D_cons(X_proét, E)` is equivalent to the rationalization of `D_cons(X_proét, 𝒪_E)` at the
powers of `ℓ` (`ProEtale.rationalizationEquivalence`), compatibly with the localization
functors (`ProEtale.rationalizationQCompEquivalenceIso`).

The statement is made on bounded constructible complexes only: on the full derived categories
`D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})` is not a localization at the morphisms with `ℓ`-power-torsion
mapping cone in general. For the noetherian coefficient rings `𝒪_E` and `E`, noetherianity of
`X` makes the bounded constructible complexes a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible_padicIntegersRingObj`,
`ProEtale.isTriangulated_boundedConstructible_continuousMapRingObj`), on which the
rationalization is defined.

Neither description is taken as a definition: `E_X` is defined by its sections, not as
`𝒪_{E,X}[1/ℓ]`, following `WeilConjectures/RefactorInstruction.tex`. Finiteness of `E` is what
makes inverting `ℓ` the right statement: `𝒪_E` is then a discrete valuation ring in which every
nonzero element divides a power of `ℓ`.

The extension of scalars along `φ` is exact
(`ProEtale.preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield`): on profinite sets
the maps `ℓ⁻ᵏ φ : 𝒪̲_E ⟶ E̲` (`Profinite.padicIntegersRingObjToContinuousMapRingObjInvPow`)
exhibit `E̲` as the sequential colimit of the multiplications by `ℓ` on `𝒪̲_E`
(`Profinite.isColimitPadicIntegersRingObjSmulSequenceCocone`), since a continuous map from a
profinite set to `E` is `ℓ⁻ᵐ` times a continuous map to `𝒪_E`
(`PadicAlgCl.exists_norm_pow_mul_le_one`); the additive left adjoint `p_X^*` keeps this colimit,
and sequential colimits of abelian sheaves are exact
(`CategoryTheory.Mod.preservesFiniteLimits_extendScalars_of_isColimit`). Hence the left derived
functor of the extension of scalars preserves bounded constructible complexes
(`ProEtale.boundedConstructible_leftDerivedExtendScalars_obj`).

## The localization statement

`ProEtale.isLocalization_boundedConstructibleExtendScalars` is an instance of
`CategoryTheory.Rationalization.isLocalization_of_models`, for `E` with the norm restricted from
`ℚ̄_ℓ` (`PadicAlgCl.normedFieldOfAlgebra`), whose closed unit ball `𝒪_E` gives the coefficient
ring `CondensedRing.integralCoeff ℓ E`:

* every bounded constructible `E_X`-complex has an integral model
  (`CondensedRing.continuousConstructible_integral_model`; Bhatt–Scholze, Lemma 6.8.13 and
  Proposition 6.8.14(2));
* multiplication by `ℓ` is invertible on `D(Mod_{E_X})` (`CondensedRing.derived_nsmul_isIso`);
* every morphism between the images of integral complexes is the image of an integral one after
  multiplication by a power of `ℓ` (`CondensedRing.continuousConstructible_clear_denominators`),
  and two integral morphisms with the same image agree after multiplication by a power of `ℓ`
  (`CondensedRing.integral_scalar_map_eq`).

The remaining `sorry`s are inherited from
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`,
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

open scoped CondensedRing

attribute [local irreducible] upperStarFromPoint Mod.extendScalars
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-! ### The inclusion `𝒪_{E,X} ⟶ E_X` -/

/-- The inclusion `𝒪̲_E ⟶ E̲` of ring objects of condensed abelian groups, for a finite
subextension `E`: the abelian sheaf morphism underlying
`Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing`. -/
noncomputable def padicIntegersRingObjToContinuousMapRingObj :
    Profinite.padicIntegersRingObj.{u} ℓ E.1 ⟶ Profinite.continuousMapRingObj E.1 :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ℓ E.1)

instance : IsMonHom (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E) :=
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing.{u} ℓ E.1)))

/-- The inclusion `𝒪_{E,X} ⟶ E_X` of coefficient ring objects on `X_proét`: the pullback along
`p_X` of the inclusion `𝒪̲_E ⟶ E̲` of condensed rings. It is a morphism of ring objects, `p_X^*`
being monoidal. -/
noncomputable abbrev padicIntegersToPadicSubfield :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X ⟶
      condensedRingObj (Profinite.continuousMapRingObj E.1) X :=
  (upperStarFromPoint X).map (padicIntegersRingObjToContinuousMapRingObj ℓ E)

end AlgebraicGeometry.ProEtale

/-! ### Flatness of `E_X` over `𝒪_{E,X}` -/

namespace Profinite

open AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The map `c_k = ℓ⁻ᵏ φ : 𝒪̲_E ⟶ E̲`, where `φ` is the inclusion. -/
noncomputable def padicIntegersRingObjToContinuousMapRingObjInvPow (k : ℕ) :
    padicIntegersRingObj.{u} ℓ E.1 ⟶ continuousMapRingObj E.1 :=
  padicIntegersRingObjToContinuousMapRingObj ℓ E ≫
    continuousMapRingObjMulLeft E.1 ((ℓ : E.1)⁻¹ ^ k)

lemma padicIntegersRingObjToContinuousMapRingObjInvPow_zero :
    padicIntegersRingObjToContinuousMapRingObjInvPow.{u} ℓ E 0 =
      padicIntegersRingObjToContinuousMapRingObj ℓ E := by
  rw [padicIntegersRingObjToContinuousMapRingObjInvPow, pow_zero,
    continuousMapRingObjMulLeft_one, Category.comp_id]

lemma nsmul_padicIntegersRingObjToContinuousMapRingObjInvPow_succ (k : ℕ) :
    ℓ • padicIntegersRingObjToContinuousMapRingObjInvPow.{u} ℓ E (k + 1) =
      padicIntegersRingObjToContinuousMapRingObjInvPow ℓ E k := by
  have hℓ : (ℓ : E.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  rw [padicIntegersRingObjToContinuousMapRingObjInvPow,
    padicIntegersRingObjToContinuousMapRingObjInvPow, ← Preadditive.comp_nsmul,
    nsmul_continuousMapRingObjMulLeft, pow_succ', ← _root_.mul_assoc, mul_inv_cancel₀ hℓ,
    _root_.one_mul]

/-- **`E̲ = colim(𝒪̲_E --ℓ--> 𝒪̲_E --ℓ--> ⋯)`**: the maps `ℓ⁻ᵏ φ : 𝒪̲_E ⟶ E̲` exhibit the condensed
abelian group `E̲` as the sequential colimit of the multiplications by `ℓ` on `𝒪̲_E`. Sectionwise,
every continuous map from a profinite set to `E` is `ℓ⁻ᵐ` times a continuous map to `𝒪_E`
(`PadicAlgCl.exists_norm_pow_mul_le_one`), and the maps `ℓ⁻ᵏ φ` are injective. -/
noncomputable def isColimitPadicIntegersRingObjSmulSequenceCocone :
    IsColimit (Mod.smulSequenceCocone ℓ
      (padicIntegersRingObjToContinuousMapRingObjInvPow.{u} ℓ E)
      (nsmul_padicIntegersRingObjToContinuousMapRingObjInvPow_succ ℓ E)) := by
  have hℓ : (ℓ : E.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (sheafToPresheaf _ _) ?_
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨x⟩ := x
    obtain ⟨m, hm⟩ := PadicAlgCl.exists_norm_pow_mul_le_one
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(E.1, PadicAlgCl ℓ)).comp x)
    have hmem (s : S.unop) : (ℓ : E.1) ^ m * x s ∈ PadicAlgCl.integers ℓ E.1 := by
      rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm, map_mul, map_pow,
        map_natCast]
      exact hm s
    refine ⟨m, ULift.up ⟨fun s ↦ ⟨_, hmem s⟩, (continuous_const.mul x.continuous).subtype_mk _⟩,
      ULift.ext (ContinuousMap.ext fun s ↦ ?_)⟩
    have key : (ℓ : E.1)⁻¹ ^ m * ((ℓ : E.1) ^ m * x s) = x s := by
      rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hℓ, one_pow, _root_.one_mul]
    exact key.symm
  · intro k x y h
    refine ⟨k, 𝟙 k, ?_⟩
    rw [CategoryTheory.Functor.map_id]
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    have hk : (ℓ : E.1)⁻¹ ^ k ≠ 0 := pow_ne_zero _ (inv_ne_zero hℓ)
    have h' (s : S.unop) :
        (ℓ : E.1)⁻¹ ^ k * (x s : E.1) = (ℓ : E.1)⁻¹ ^ k * (y s : E.1) :=
      congrArg (fun z : ULift.{u + 1} C(S.unop, E.1) ↦ z.down s) h
    obtain rfl : x = y := ContinuousMap.ext fun s ↦ Subtype.ext (mul_left_cancel₀ hk (h' s))
    rfl

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

open scoped CondensedRing

section

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- **Flatness of `E_X` over `𝒪_{E,X}`**: the extension of scalars along the inclusion
`𝒪_{E,X} ⟶ E_X` is exact. Indeed `E_X = p_X^* E̲` is the sequential colimit of the
multiplications by `ℓ` on `𝒪_{E,X} = p_X^* 𝒪̲_E`, `p_X^*` being an additive left adjoint, so
`E_X ⊗_{𝒪_{E,X}} M = colim(M --ℓ--> M --ℓ--> ⋯)`, and sequential colimits of abelian sheaves are
exact. -/
instance preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield (X : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)) := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  have := AB5OfSize_of_univLE.{0, 0} (Sheaf (ProEt.topology X) Ab.{u + 1})
  exact Mod.preservesFiniteLimits_extendScalars_of_isColimit _
    (Mod.isColimitSmulSequenceCoconeMap (upperStarFromPoint X) _
      (Profinite.isColimitPadicIntegersRingObjSmulSequenceCocone ℓ E))
    (by rw [Profinite.padicIntegersRingObjToContinuousMapRingObjInvPow_zero])

end

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-! ### Extension of scalars on bounded constructible complexes -/

/-- The derived extension of scalars `E ⊗ᴸ_{𝒪_E} - : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})` preserves
bounded constructible complexes. -/
lemma boundedConstructible_derivedExtendScalars_obj
    (K : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X)
      ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.obj K.obj) :=
  boundedConstructible_leftDerivedExtendScalars_obj _ _ _ K.obj K.property

/-- The derived extension of scalars `E ⊗ᴸ_{𝒪_E} - : D_cons(X_proét, 𝒪_E) ⥤ D_cons(X_proét, E)`
on bounded constructible complexes: the restriction of
`L(extendScalars (padicIntegersToPadicSubfield X ℓ E))`. -/
noncomputable def boundedConstructibleExtendScalars :
    Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E.1⟧ ⥤
      Dᵇc(X)⟦Profinite.continuousMapRingObj E.1⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙
      (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor)
    fun K ↦ boundedConstructible_derivedExtendScalars_obj X ℓ E K

/-- The restricted derived extension of scalars is compatible with the inclusions. -/
noncomputable def boundedConstructibleExtendScalarsCompatibility :
    boundedConstructibleExtendScalars X ℓ E ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙
        (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor :=
  ObjectProperty.liftCompιIso _ _ _

/-! ### `E` as `𝒪_E` with `ℓ` inverted -/

variable [TopologicalSpace.NoetherianSpace X]

/-- On a topologically noetherian scheme, the derived extension of scalars
`E ⊗ᴸ_{𝒪_E} - : D_cons(X_proét, 𝒪_E) ⥤ D_cons(X_proét, E)` on bounded constructible complexes
is a localization functor with respect to the morphisms whose mapping cone is killed by some
power of `ℓ`: the bounded constructible `E`-coefficient derived category is the bounded
constructible `𝒪_E`-coefficient one with `ℓ` inverted. -/
instance isLocalization_boundedConstructibleExtendScalars :
    (boundedConstructibleExtendScalars X ℓ E).IsLocalization
      (Rationalization.W (Submonoid.powers (ℓ : ℤ))
        (Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  let F := Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)
  let L := F.leftDerivedFunctor
  let D := F.mapDerivedCategory
  let e : L ≅ D := F.leftDerivedFunctorIsoMapDerivedCategory
  let : L.CommShift ℤ := Functor.CommShift.ofIso e.symm ℤ
  let := Functor.CommShift.ofIso_compatibility e.symm ℤ
  have : L.IsTriangulated := Functor.isTriangulated_of_iso e.symm
  exact Rationalization.isLocalization_of_models ℓ
    (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))
    (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X))
    L (boundedConstructibleExtendScalars X ℓ E)
    (boundedConstructibleExtendScalarsCompatibility X ℓ E)
    (CondensedRing.continuousConstructible_integral_model ℓ E.1 X)
    (CondensedRing.derived_nsmul_isIso ℓ E.1 X)
    (CondensedRing.continuousConstructible_clear_denominators ℓ E.1 X)
    (CondensedRing.integral_scalar_map_eq ℓ E.1 X)

/-- The bounded constructible `E`-coefficient derived category `D_cons(X_proét, E)` is
equivalent to the rationalization of the bounded constructible `𝒪_E`-coefficient derived
category `D_cons(X_proét, 𝒪_E)` at the powers of `ℓ`. -/
noncomputable def rationalizationEquivalence :
    Rationalization (Submonoid.powers (ℓ : ℤ))
        (Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) ≌
      Dᵇc(X)⟦Profinite.continuousMapRingObj E.1⟧ :=
  Localization.uniq (Rationalization.Q _ _) (boundedConstructibleExtendScalars X ℓ E)
    (Rationalization.W (Submonoid.powers (ℓ : ℤ)) _)

/-- Under `rationalizationEquivalence`, the localization functor to the rationalization
corresponds to the derived extension of scalars `E ⊗ᴸ_{𝒪_E} -` on bounded constructible
complexes. -/
noncomputable def rationalizationQCompEquivalenceIso :
    Rationalization.Q (Submonoid.powers (ℓ : ℤ)) _ ⋙ (rationalizationEquivalence X ℓ E).functor ≅
      boundedConstructibleExtendScalars X ℓ E :=
  Localization.compUniqFunctor (Rationalization.Q _ _) _
    (Rationalization.W (Submonoid.powers (ℓ : ℤ)) _)

end AlgebraicGeometry.ProEtale
