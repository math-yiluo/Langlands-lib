import Langlands.MathlibBase
import Langlands.Correspondence.Laumon.CurveRiemannHurwitz
import Langlands.CommutativeAlgebra.IntegralClosureDvrCenter
import Langlands.CommutativeAlgebra.TameDifferent
import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
import WeilConjectures.AlgebraicGeometry.NormalizationCover
import WeilConjectures.Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# The semilocal ring of a finite morphism of curves and the local different exponent

Let `f : Y ⟶ X` be a finite morphism of integral schemes, smooth of relative dimension one over a
field `κ`, mapping the generic point to the generic point, with `κ(Y) / κ(X)` separable. For a
point `y` of `Y` let `A = 𝒪_{X,f(y)}` and let `B = curveSemilocalRing f y` be the integral
closure of `A` in `κ(Y)`. This file proves the facts about `B` and `curveDifferentExponent` that
every use of the local different exponent needs:

* at every point `y`: `A` is a Dedekind domain (`isDedekindDomain_stalk`); `B` is a Dedekind
  domain (`isDedekindDomain_curveSemilocalRing`), torsion-free (`isTorsionFree_curveSemilocalRing`)
  and finite (`finite_curveSemilocalRing`) over `A`; `𝒪_{X,f(y)} → κ(X) → κ(Y)` is a tower
  (`isScalarTower_functionField`), and `Frac B` is separable over `Frac A`
  (`isSeparable_fractionRing_curveSemilocalRing`);
* at a closed point `y`: `A` is a discrete valuation ring (`isDiscreteValuationRing_stalk_apply`),
  `𝔓_y = B ∩ 𝔪_y` (`curvePrime`) is a maximal ideal of `B` over `𝔪_{f(y)}`, and `𝒪_{Y,y}` is the
  localization of `B` at `𝔓_y` (`isLocalization_curvePrime`);
* at a closed point `y`: `curveDifferentExponent f y` is the multiplicity of `𝔓_y` in the
  factorization of `differentIdeal A B` (`curveDifferentExponent_eq_count`), and
  `f.ramificationIndex y` is the ramification index `Ideal.ramificationIdx` of `𝔓_y` over `A`
  (`ramificationIndex_eq_ramificationIdx`).
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing UniqueFactorizationMonoid Order
open Langlands.CommutativeAlgebra.IntegralClosureDvrCenter

namespace Langlands.Henniart.Laumon

attribute [local instance] curveStalkFunctionFieldAlgebra

section Stalk

variable (κ : Type u) [Field κ] {X : Scheme.{u}} [X.Over (Spec (.of κ))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))] [IsIntegral X]

include κ in
/-- Every local ring of a smooth integral curve is a Dedekind domain: it is a noetherian valuation
ring, hence a principal ideal domain. -/
theorem isDedekindDomain_stalk (x : X) : IsDedekindDomain (X.presheaf.stalk x) := by
  have : Smooth (X ↘ Spec (.of κ)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of κ))
  have := Scheme.valuationRing_stalk (X ↘ Spec (.of κ)) x
  infer_instance

include κ in
/-- The local ring of a smooth curve at a closed point is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk {x : X} (hx : IsClosed {x}) :
    IsDiscreteValuationRing (X.presheaf.stalk x) :=
  (Scheme.isDiscreteValuationRing_stalk_of_isClosed (X ↘ Spec (.of κ)) hx).2

end Stalk

section StalkAlgebra

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}` as an algebra structure. -/
abbrev curveStalkAlgebra (y : Y) : Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
  (f.stalkMap y).hom.toAlgebra

attribute [local instance] curveStalkAlgebra

/-- The stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}` is a local homomorphism. -/
theorem isLocalHom_curveStalkAlgebra (y : Y) :
    IsLocalHom (algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)) :=
  inferInstanceAs (IsLocalHom (f.stalkMap y).hom)

/-- The tower `𝒪_{X,f(y)} → 𝒪_{Y,y} → κ(Y)` defining `curveStalkFunctionFieldAlgebra`. -/
theorem isScalarTower_curveStalkAlgebra [IsIntegral X] [IsIntegral Y] (y : Y) :
    IsScalarTower (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) Y.functionField :=
  IsScalarTower.of_algebraMap_eq' rfl

end StalkAlgebra

attribute [local instance] curveStalkAlgebra isScalarTower_curveStalkAlgebra
  isLocalHom_curveStalkAlgebra

section Tower

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
  (hgen : f (genericPoint Y) = genericPoint X)

/-- The square formed by the stalk map of `f` at `y`, the map of function fields of `f` and the
maps from the stalks to the function fields commutes. -/
theorem stalkSpecializes_functionFieldMap (y : Y) :
    X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ (f y))) ≫
        f.functionFieldMap hgen =
      f.stalkMap y ≫
        Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ y)) := by
  rw [Scheme.Hom.functionFieldMap, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp,
    ← Scheme.Hom.stalkSpecializes_stalkMap]

/-- The map `κ(X) → κ(Y)` of function fields is compatible with the stalk map
`𝒪_{X,f(y)} → 𝒪_{Y,y}`. -/
theorem functionFieldMap_algebraMap (y : Y) (a : X.presheaf.stalk (f y)) :
    (f.functionFieldMap hgen).hom (algebraMap _ X.functionField a) =
      algebraMap (Y.presheaf.stalk y) Y.functionField (f.stalkMap y a) := by
  have h := CommRingCat.hom_ext_iff.mp (stalkSpecializes_functionFieldMap f hgen y)
  exact congr($h a)

/-- The tower `𝒪_{X,f(y)} → κ(X) → κ(Y)`, where `κ(X) → κ(Y)` is the map of function fields
of `f` and `𝒪_{X,f(y)} → κ(Y)` is `curveStalkFunctionFieldAlgebra`. -/
theorem isScalarTower_functionField (y : Y) :
    letI := (f.functionFieldMap hgen).hom.toAlgebra
    IsScalarTower (X.presheaf.stalk (f y)) X.functionField Y.functionField := by
  let := (f.functionFieldMap hgen).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a ↦ (functionFieldMap_algebraMap f hgen y a).symm

include hgen in
/-- The map `𝒪_{X,f(y)} → κ(Y)` is injective. -/
theorem algebraMap_stalk_functionField_injective (y : Y) :
    Function.Injective (algebraMap (X.presheaf.stalk (f y)) Y.functionField) := by
  let := (f.functionFieldMap hgen).hom.toAlgebra
  have := isScalarTower_functionField f hgen y
  rw [IsScalarTower.algebraMap_eq (X.presheaf.stalk (f y)) X.functionField Y.functionField,
    RingHom.coe_comp]
  exact (algebraMap X.functionField Y.functionField).injective.comp
    (IsFractionRing.injective _ _)

include hgen in
/-- The semilocal ring `curveSemilocalRing f y` is torsion-free over `𝒪_{X,f(y)}`. -/
theorem isTorsionFree_curveSemilocalRing (y : Y) :
    Module.IsTorsionFree (X.presheaf.stalk (f y)) (curveSemilocalRing f y) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  intro a b h
  apply algebraMap_stalk_functionField_injective f hgen y
  rw [IsScalarTower.algebraMap_apply _ (curveSemilocalRing f y) Y.functionField, h,
    ← IsScalarTower.algebraMap_apply]

include hgen in
/-- `κ(Y)` is algebraic over `𝒪_{X,f(y)}`. -/
theorem isAlgebraic_stalk_functionField [IsFinite f] (y : Y) :
    Algebra.IsAlgebraic (X.presheaf.stalk (f y)) Y.functionField := by
  let := (f.functionFieldMap hgen).hom.toAlgebra
  have := isScalarTower_functionField f hgen y
  have : FiniteDimensional X.functionField Y.functionField := f.finiteDimensional_functionField hgen
  have := IsLocalization.isAlgebraic X.functionField (nonZeroDivisors (X.presheaf.stalk (f y)))
  exact Algebra.IsAlgebraic.trans _ X.functionField _

/-- The ideal `𝔓_y = B ∩ 𝔪_y` of the semilocal ring `B = curveSemilocalRing f y`, generated by
the elements of `B` that are images of elements of the maximal ideal of `𝒪_{Y,y}`
(`Langlands.CommutativeAlgebra.IntegralClosureDvrCenter.centerIdeal`). -/
def curvePrime (y : Y) : Ideal (curveSemilocalRing f y) :=
  centerIdeal (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) Y.functionField

/-- The inclusion `B ⊆ 𝒪_{Y,y}` of subrings of `κ(Y)`, for `𝒪_{Y,y}` integrally closed. -/
def curveSemilocalRingToStalk (y : Y) [IsIntegrallyClosed (Y.presheaf.stalk y)] :
    curveSemilocalRing f y →+* Y.presheaf.stalk y :=
  toRing (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) Y.functionField

@[simp]
theorem algebraMap_curveSemilocalRingToStalk (y : Y) [IsIntegrallyClosed (Y.presheaf.stalk y)]
    (b : curveSemilocalRing f y) :
    algebraMap (Y.presheaf.stalk y) Y.functionField (curveSemilocalRingToStalk f y b) = b :=
  algebraMap_toRing b

end Tower

section Semilocal

variable (κ : Type u) [Field κ] {X Y : Scheme.{u}} [X.Over (Spec (.of κ))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))] [IsIntegral X] [IsIntegral Y]
  (f : Y ⟶ X) [IsFinite f] (hgen : f (genericPoint Y) = genericPoint X)
  (hsep : letI := (f.functionFieldMap hgen).hom.toAlgebra
      Algebra.IsSeparable X.functionField Y.functionField)

include κ hsep in
/-- At every point `y` of `Y`, the integral closure `curveSemilocalRing f y` of `𝒪_{X,f(y)}` in
`κ(Y)` is a Dedekind domain. -/
theorem isDedekindDomain_curveSemilocalRing (y : Y) :
    IsDedekindDomain (curveSemilocalRing f y) := by
  let := (f.functionFieldMap hgen).hom.toAlgebra
  have := isScalarTower_functionField f hgen y
  have : FiniteDimensional X.functionField Y.functionField := f.finiteDimensional_functionField hgen
  have : Algebra.IsSeparable X.functionField Y.functionField := hsep
  have := isDedekindDomain_stalk κ (f y)
  exact integralClosure.isDedekindDomain _ X.functionField _

include κ hsep in
/-- At every point `y` of `Y`, `curveSemilocalRing f y` is a finite `𝒪_{X,f(y)}`-module. -/
theorem finite_curveSemilocalRing (y : Y) :
    Module.Finite (X.presheaf.stalk (f y)) (curveSemilocalRing f y) := by
  let := (f.functionFieldMap hgen).hom.toAlgebra
  have := isScalarTower_functionField f hgen y
  have : FiniteDimensional X.functionField Y.functionField := f.finiteDimensional_functionField hgen
  have : Algebra.IsSeparable X.functionField Y.functionField := hsep
  have := isDedekindDomain_stalk κ (f y)
  exact IsIntegralClosure.finite _ X.functionField Y.functionField _

attribute [local instance] FractionRing.liftAlgebra in
include κ hsep in
/-- `κ(Y) / κ(X)` separable makes the fraction field of `curveSemilocalRing f y` separable over
the fraction field of `𝒪_{X,f(y)}` (the form of the hypothesis in Mathlib's results on
`differentIdeal`). -/
theorem isSeparable_fractionRing_curveSemilocalRing (y : Y) :
    haveI := isDedekindDomain_curveSemilocalRing κ f hgen hsep y
    haveI := isTorsionFree_curveSemilocalRing f hgen y
    Algebra.IsSeparable (FractionRing (X.presheaf.stalk (f y)))
      (FractionRing (curveSemilocalRing f y)) := by
  have := isDedekindDomain_curveSemilocalRing κ f hgen hsep y
  have := isTorsionFree_curveSemilocalRing f hgen y
  have := isDedekindDomain_stalk κ (f y)
  let := (f.functionFieldMap hgen).hom.toAlgebra
  have := isScalarTower_functionField f hgen y
  have : FiniteDimensional X.functionField Y.functionField := f.finiteDimensional_functionField hgen
  have : Algebra.IsSeparable X.functionField Y.functionField := hsep
  have := integralClosure.isFractionRing_of_finite_extension (A := X.presheaf.stalk (f y))
    X.functionField Y.functionField
  exact Langlands.CommutativeAlgebra.TameDifferent.isSeparable_fractionRing _ X.functionField
    Y.functionField

variable [IsLocallyNoetherian Y]

include κ hsep in
/-- `curveDifferentExponent f y` takes the first branch of its definition. -/
theorem curveDifferentExponent_eq (y : Y) :
    haveI := isDedekindDomain_curveSemilocalRing κ f hgen hsep y
    haveI := isTorsionFree_curveSemilocalRing f hgen y
    curveDifferentExponent f y =
      (sInf ((fun d : curveSemilocalRing f y ↦ Y.ord (d : Y.functionField) y) ''
        {d | d ∈ differentIdeal (X.presheaf.stalk (f y)) (curveSemilocalRing f y) ∧
          d ≠ 0})).toNat := by
  rw [curveDifferentExponent, dite_eq_left ⟨isDedekindDomain_curveSemilocalRing κ f hgen hsep y,
    isTorsionFree_curveSemilocalRing f hgen y⟩]

end Semilocal

section Closed

variable (κ : Type u) [Field κ] {X Y : Scheme.{u}} [X.Over (Spec (.of κ))]
  [Y.Over (Spec (.of κ))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))] [IsIntegral X]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of κ))] [IsIntegral Y]
  (f : Y ⟶ X) [IsFinite f] (hgen : f (genericPoint Y) = genericPoint X)
  (hsep : letI := (f.functionFieldMap hgen).hom.toAlgebra
      Algebra.IsSeparable X.functionField Y.functionField)
  (y : Y) (hy : IsClosed {y})

include κ hy in
omit [Y.Over (Spec (.of κ))] [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of κ))] [IsIntegral Y] in
/-- At a closed point `y`, the local ring `𝒪_{X,f(y)}` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk_apply :
    IsDiscreteValuationRing (X.presheaf.stalk (f y)) :=
  isDiscreteValuationRing_stalk κ (f.isClosed_singleton_apply hy)

include κ hy in
omit [Y.Over (Spec (.of κ))] [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of κ))] [IsIntegral Y] in
/-- At a closed point `y`, the maximal ideal of `𝒪_{X,f(y)}` is nonzero. -/
theorem maximalIdeal_stalk_apply_ne_bot : maximalIdeal (X.presheaf.stalk (f y)) ≠ ⊥ :=
  have := isDiscreteValuationRing_stalk_apply κ f y hy
  IsDiscreteValuationRing.not_a_field _

include κ in
omit [X.Over (Spec (.of κ))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))] [IsFinite f] in
/-- `𝔓_y` lies over the maximal ideal of `𝒪_{X,f(y)}`. -/
theorem curvePrime_liesOver :
    (curvePrime f y).LiesOver (maximalIdeal (X.presheaf.stalk (f y))) := by
  have := isDedekindDomain_stalk κ y
  exact centerIdeal_liesOver

include κ hsep hy in
/-- At a closed point `y`, `𝔓_y` is a maximal ideal of `curveSemilocalRing f y`. -/
theorem isMaximal_curvePrime : (curvePrime f y).IsMaximal := by
  have := isDedekindDomain_curveSemilocalRing κ f hgen hsep y
  have := isDiscreteValuationRing_stalk κ hy
  exact centerIdeal_isMaximal (maximalIdeal_stalk_apply_ne_bot κ f y hy)
    (algebraMap_stalk_functionField_injective f hgen y)

include hsep hy in
/-- **`𝒪_{Y,y}` is the localization of `B = curveSemilocalRing f y` at `𝔓_y`**, for the inclusion
`curveSemilocalRingToStalk f y : B → 𝒪_{Y,y}` of subrings of `κ(Y)`
(`algebraMap_curveSemilocalRingToStalk`). -/
theorem isLocalization_curvePrime :
    haveI := isDedekindDomain_stalk κ y
    haveI := (isMaximal_curvePrime κ f hgen hsep y hy).isPrime
    letI := (curveSemilocalRingToStalk f y).toAlgebra
    IsLocalization.AtPrime (Y.presheaf.stalk y) (curvePrime f y) := by
  have := isDedekindDomain_curveSemilocalRing κ f hgen hsep y
  have := isDiscreteValuationRing_stalk κ hy
  have := isAlgebraic_stalk_functionField f hgen y
  exact isLocalization_atPrime _ _ _ (maximalIdeal_stalk_apply_ne_bot κ f y hy)
    (algebraMap_stalk_functionField_injective f hgen y)

variable [IsLocallyNoetherian Y]

include hsep hy in
/-- **The local different exponent as an exponent of the different ideal.** At a closed point
`y`, `curveDifferentExponent f y` is the multiplicity of `𝔓_y` in the factorization of the
different ideal of `curveSemilocalRing f y` over `𝒪_{X,f(y)}`. -/
theorem curveDifferentExponent_eq_count :
    haveI := isDedekindDomain_curveSemilocalRing κ f hgen hsep y
    haveI := isTorsionFree_curveSemilocalRing f hgen y
    curveDifferentExponent f y =
      (normalizedFactors (differentIdeal (X.presheaf.stalk (f y))
        (curveSemilocalRing f y))).count (curvePrime f y) := by
  have := isDedekindDomain_curveSemilocalRing κ f hgen hsep y
  have := isTorsionFree_curveSemilocalRing f hgen y
  have := isDiscreteValuationRing_stalk κ hy
  have := isAlgebraic_stalk_functionField f hgen y
  have hA := maximalIdeal_stalk_apply_ne_bot κ f y hy
  have hinj := algebraMap_stalk_functionField_injective f hgen y
  have hcoh : coheight y = 1 := Scheme.coheight_eq_one_of_isClosed (Y ↘ Spec (.of κ)) hy
  rw [curveDifferentExponent_eq κ f hgen hsep y]
  set D := differentIdeal (X.presheaf.stalk (f y)) (curveSemilocalRing f y)
  by_cases hD : D = ⊥
  · have : {d | d ∈ D ∧ d ≠ 0} = ∅ := by
      ext d
      simp only [hD, Ideal.mem_bot, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and, not_not, imp_self]
    rw [this, Set.image_empty, Int.csInf_empty, hD, ← Ideal.zero_eq_bot, normalizedFactors_zero,
      Multiset.count_zero]
    rfl
  obtain ⟨⟨d₀, hd₀, hd₀0, hv₀⟩, hle⟩ :=
    isLeast_count_normalizedFactors (O := Y.presheaf.stalk y) hA hinj D hD
  set n := (normalizedFactors D).count (centerIdeal (X.presheaf.stalk (f y))
    (Y.presheaf.stalk y) Y.functionField)
  have hord : ∀ d : curveSemilocalRing f y, d ≠ 0 → Y.ord (d : Y.functionField) y =
      ((IsDiscreteValuationRing.addVal _ (toRing (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
        Y.functionField d)).toNat : ℤ) := by
    intro d hd
    have hd' : toRing (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) Y.functionField d ≠ 0 :=
      (map_ne_zero_iff _ toRing_injective).mpr hd
    rw [← algebraMap_toRing (O := Y.presheaf.stalk y) d, Scheme.ord_algebraMap_stalk hcoh hd',
      Ring.ord_eq_addVal]
  have hleast : IsLeast ((fun d : curveSemilocalRing f y ↦ Y.ord (d : Y.functionField) y) ''
      {d | d ∈ D ∧ d ≠ 0}) (n : ℤ) := by
    refine ⟨⟨d₀, ⟨hd₀, hd₀0⟩, ?_⟩, ?_⟩
    · simp only
      rw [hord d₀ hd₀0, hv₀, ENat.toNat_natCast]
    · rintro _ ⟨d, ⟨hd, hd0⟩, rfl⟩
      simp only
      rw [hord d hd0]
      have h1 := hle ⟨d, hd, hd0, rfl⟩
      have hfin : IsDiscreteValuationRing.addVal _ (toRing (X.presheaf.stalk (f y))
          (Y.presheaf.stalk y) Y.functionField d) ≠ ⊤ := by
        rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
        exact (map_ne_zero_iff _ toRing_injective).mpr hd0
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
      rw [← hm] at h1 ⊢
      rw [ENat.toNat_natCast]
      exact_mod_cast h1
  rw [hleast.csInf_eq, Int.toNat_natCast]
  rfl

include κ hsep hy in
/-- **The ramification index as Mathlib's ramification index.** At a closed point `y`, the
ramification index `f.ramificationIndex y` is the ramification index of `𝔓_y` over the maximal
ideal of `𝒪_{X,f(y)}`. -/
theorem ramificationIndex_eq_ramificationIdx :
    f.ramificationIndex y = ((curvePrime f y).ramificationIdx (X.presheaf.stalk (f y)) : ℤ) := by
  have := isDedekindDomain_curveSemilocalRing κ f hgen hsep y
  have := isDiscreteValuationRing_stalk κ hy
  have := isDiscreteValuationRing_stalk_apply κ f y hy
  have := isAlgebraic_stalk_functionField f hgen y
  have hA := maximalIdeal_stalk_apply_ne_bot κ f y hy
  have hinj := algebraMap_stalk_functionField_injective f hgen y
  have hcoh : coheight y = 1 := Scheme.coheight_eq_one_of_isClosed (Y ↘ Spec (.of κ)) hy
  have hex : ∃ t, maximalIdeal (X.presheaf.stalk (f y)) = Ideal.span {t} :=
    ⟨_, ((IsPrincipalIdealRing.principal (maximalIdeal _)).span_singleton_generator).symm⟩
  set t := Classical.epsilon fun t ↦ maximalIdeal (X.presheaf.stalk (f y)) = Ideal.span {t}
    with ht_def
  have ht : maximalIdeal (X.presheaf.stalk (f y)) = Ideal.span {t} := Classical.epsilon_spec hex
  have ht0 : algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) t ≠ 0 := by
    intro h
    apply hA
    rw [ht, Ideal.span_singleton_eq_bot]
    apply hinj
    rw [IsScalarTower.algebraMap_apply _ (Y.presheaf.stalk y) Y.functionField, h, map_zero,
      map_zero]
  have hram := ramificationIdx_centerIdeal (O := Y.presheaf.stalk y) hA hinj t ht
  rw [Scheme.Hom.ramificationIndex, ← ht_def]
  change Y.ord (algebraMap (Y.presheaf.stalk y) Y.functionField
    (algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) t)) y = _
  rw [Scheme.ord_algebraMap_stalk hcoh ht0, Ring.ord_eq_addVal, ← hram, ENat.toNat_natCast]
  rfl

end Closed

end Langlands.Henniart.Laumon
