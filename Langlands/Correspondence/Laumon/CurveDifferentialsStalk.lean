import Langlands.MathlibBase
import Langlands.Correspondence.Laumon.CurveSemilocalRing
import Langlands.Correspondence.Laumon.TameCurveDifferent
import Langlands.CommutativeAlgebra.KaehlerDifferent
import Langlands.CommutativeAlgebra.KaehlerMapBaseChange
import WeilConjectures.AlgebraicGeometry.SmoothUniformizer

/-!
# Stalks of the differentials of a finite separable morphism of curves

For a morphism `f : Y ⟶ X` of smooth curves over a field `κ`, mapping the generic point to the
generic point with `κ(Y) / κ(X)` separable: the map
`𝒪_{Y,y} ⊗ Ω_{𝒪_{X,f(y)}/κ} → Ω_{𝒪_{Y,y}/κ}` is injective at every point, and, for `f` finite,
`κ` perfect and `y` closed, its cokernel has length `curveDifferentExponent f y`. The length is
the curve case of Serre's characterization of the different by relative differentials
(*Local Fields*, III §7, Prop. 14).
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Langlands.CommutativeAlgebra

namespace Langlands.Henniart.Laumon

attribute [local instance] curveStalkFunctionFieldAlgebra curveStalkAlgebra
  isScalarTower_curveStalkAlgebra

section Smooth

variable (κ : Type u) [Field κ] {X : Scheme.{u}} [X.Over (Spec (.of κ))]

/-- The local rings of a smooth `κ`-scheme are formally smooth `κ`-algebras. -/
theorem formallySmooth_stalk [Smooth (X ↘ Spec (.of κ))] (x : X) :
    letI := stalkAlgebraOver κ X x
    Algebra.FormallySmooth κ (X.presheaf.stalk x) :=
  ((X ↘ Spec (.of κ)).mem_smoothLocus_iff_formallySmooth x).mp
    (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial)

end Smooth

section Etale

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsFinite f]
  (hgen : f (genericPoint Y) = genericPoint X)
  (hsep : letI := (f.functionFieldMap hgen).hom.toAlgebra
      Algebra.IsSeparable X.functionField Y.functionField)

omit [IsFinite f] in
include hsep in
/-- `κ(Y)` is a formally étale `𝒪_{X,f(y)}`-algebra: it is an algebraic separable extension of
the localization `κ(X)` of `𝒪_{X,f(y)}`. Finiteness of `f` is not needed here. -/
theorem formallyEtale_stalk_functionField (y : Y) :
    Algebra.FormallyEtale (X.presheaf.stalk (f y)) Y.functionField := by
  let := (f.functionFieldMap hgen).hom.toAlgebra
  have := isScalarTower_functionField f hgen y
  have : Algebra.IsSeparable X.functionField Y.functionField := hsep
  have : Algebra.FormallyEtale (X.presheaf.stalk (f y)) X.functionField :=
    .of_isLocalization (nonZeroDivisors _)
  have : Algebra.FormallyEtale X.functionField Y.functionField := .of_isSeparable _ _
  exact .comp _ X.functionField _

end Etale

section Stalk

variable (κ : Type u) [Field κ] {X Y : Scheme.{u}} [X.Over (Spec (.of κ))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))] [IsIntegral X] [IsIntegral Y]
  (f : Y ⟶ X) [IsFinite f] (hgen : f (genericPoint Y) = genericPoint X)
  (hsep : letI := (f.functionFieldMap hgen).hom.toAlgebra
      Algebra.IsSeparable X.functionField Y.functionField)

omit [IsFinite f] in
include hsep in
/-- **Injectivity on stalks.** At every point `y`, the map
`𝒪_{Y,y} ⊗ Ω_{𝒪_{X,f(y)}/κ} → Ω_{𝒪_{Y,y}/κ}` is injective. -/
theorem isStalkDifferentialsMapInjective_of_isSeparable (y : Y) :
    IsStalkDifferentialsMapInjective κ f y := by
  let : Algebra κ (X.presheaf.stalk (f y)) := stalkAlgebraOver κ X (f y)
  let : Algebra κ (Y.presheaf.stalk y) :=
    ((algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)).comp
      (algebraMap κ (X.presheaf.stalk (f y)))).toAlgebra
  have : IsScalarTower κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra κ Y.functionField :=
    ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp
      (algebraMap κ (Y.presheaf.stalk y))).toAlgebra
  have : IsScalarTower κ (Y.presheaf.stalk y) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower κ (X.presheaf.stalk (f y)) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Smooth (X ↘ Spec (.of κ)) := SmoothOfRelativeDimension.smooth 1 _
  have : Algebra.FormallySmooth κ (X.presheaf.stalk (f y)) := formallySmooth_stalk κ (f y)
  have := formallyEtale_stalk_functionField f hgen hsep y
  exact KaehlerMapBaseChange.mapBaseChange_injective κ _ _ Y.functionField
    (IsFractionRing.injective _ _)

variable [Y.Over (Spec (.of κ))] [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of κ))]

omit [X.Over (Spec (.of κ))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))] [IsFinite f] in
/-- The inclusion `curveSemilocalRing f y ⊆ 𝒪_{Y,y}` is compatible with the algebra structures
over `𝒪_{X,f(y)}`. -/
theorem isScalarTower_curveSemilocalRingToStalk (y : Y) :
    haveI := isDedekindDomain_stalk κ y
    letI := (curveSemilocalRingToStalk f y).toAlgebra
    IsScalarTower (X.presheaf.stalk (f y)) (curveSemilocalRing f y) (Y.presheaf.stalk y) := by
  have := isDedekindDomain_stalk κ y
  let := (curveSemilocalRingToStalk f y).toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
  apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
  change _ = algebraMap (Y.presheaf.stalk y) Y.functionField
    (curveSemilocalRingToStalk f y (algebraMap _ _ a))
  rw [algebraMap_curveSemilocalRingToStalk]
  rfl

variable [IsLocallyNoetherian Y]

include hsep in
/-- **The length of the cokernel at a closed point** (Serre, *Local Fields*, III §7, Prop. 14):
for `κ` perfect and `y` closed, the cokernel of `𝒪_{Y,y} ⊗ Ω_{𝒪_{X,f(y)}/κ} → Ω_{𝒪_{Y,y}/κ}`
has length `curveDifferentExponent f y`. -/
theorem stalkDifferentialsCokernelLength_eq [PerfectField κ] (y : Y) (hy : IsClosed {y}) :
    stalkDifferentialsCokernelLength κ f y = curveDifferentExponent f y := by
  let : Algebra κ (X.presheaf.stalk (f y)) := stalkAlgebraOver κ X (f y)
  let : Algebra κ (Y.presheaf.stalk y) :=
    ((algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)).comp
      (algebraMap κ (X.presheaf.stalk (f y)))).toAlgebra
  have : IsScalarTower κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  change Module.length (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄κ] ⧸ LinearMap.range
    (KaehlerDifferential.mapBaseChange κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y))) = _
  rw [KaehlerMapBaseChange.length_quot_range_mapBaseChange]
  have := isDedekindDomain_curveSemilocalRing κ f hgen hsep y
  have := isTorsionFree_curveSemilocalRing f hgen y
  have := finite_curveSemilocalRing κ f hgen hsep y
  have := isDedekindDomain_stalk κ (f y)
  have := isDedekindDomain_stalk κ y
  have := isMaximal_curvePrime κ f hgen hsep y hy
  have := curvePrime_liesOver κ f y
  have := isSeparable_residueField_curvePrime κ f y hgen hsep hy
  have := isSeparable_fractionRing_curveSemilocalRing κ f hgen hsep y
  let := (curveSemilocalRingToStalk f y).toAlgebra
  have := isScalarTower_curveSemilocalRingToStalk κ f y
  have := isLocalization_curvePrime κ f hgen hsep y hy
  have hA := maximalIdeal_stalk_apply_ne_bot κ f y hy
  have hP : curvePrime f y ≠ ⊥ := by
    intro h
    apply hA
    rw [Ideal.over_def (curvePrime f y) (maximalIdeal (X.presheaf.stalk (f y))), h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  rw [KaehlerDifferent.length_kaehler_eq_count (maximalIdeal (X.presheaf.stalk (f y))) hA
    (curvePrime f y) hP, curveDifferentExponent_eq_count κ f hgen hsep y hy]

end Stalk

end Langlands.Henniart.Laumon
