import Langlands.MathlibBase
import Langlands.Correspondence.Laumon.CurveSemilocalRing
import Langlands.CommutativeAlgebra.TameDifferent
import WeilConjectures.PointCount

/-!
# The tame different of a finite separable morphism of curves

`tameCurveDifferentStatement` proves `TameCurveDifferentStatement`: for a finite morphism
`f : Y ⟶ X` of smooth proper geometrically connected curves over a perfect field `κ`, mapping the
generic point to the generic point with `κ(Y) / κ(X)` separable, and a closed point `y` of `Y`
whose ramification index `e_y` is invertible in `κ`, the local different exponent
`curveDifferentExponent f y` is `e_y - 1` (Serre, *Local Fields*, III §6, Prop. 13). The proof
applies the theorem
`Langlands.CommutativeAlgebra.TameDifferent.count_normalizedFactors_differentIdeal_of_isSeparable`
to the semilocal ring `curveSemilocalRing f y` and the prime `curvePrime f y`, through the
identifications of the module `Langlands.Correspondence.Laumon.CurveSemilocalRing`.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Langlands.Henniart.Laumon

attribute [local instance] curveStalkFunctionFieldAlgebra Ideal.Quotient.field

section Residue

variable (κ : Type u) [Field κ] {X Y : Scheme.{u}} [X.Over (Spec (.of κ))]
  (f : Y ⟶ X) (y : Y)

/-- A natural number that is nonzero in `κ` is nonzero in the residue field of `𝒪_{X,f(y)}`,
which is an extension of `κ`. -/
theorem natCast_ne_zero_residueField (n : ℕ) (hn : (n : κ) ≠ 0) :
    (n : X.presheaf.stalk (f y) ⧸ maximalIdeal (X.presheaf.stalk (f y))) ≠ 0 := by
  let φ : κ →+* X.presheaf.stalk (f y) ⧸ maximalIdeal (X.presheaf.stalk (f y)) :=
    (X ↘ Spec (.of κ)).residueFieldAlgebraMap (f y)
  rw [← map_natCast φ n]
  exact (map_ne_zero φ).mpr hn

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))] [IsIntegral X] [IsIntegral Y]
  [Y.Over (Spec (.of κ))] [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of κ))]
  [IsFinite f] (hgen : f (genericPoint Y) = genericPoint X)
  (hsep : letI := (f.functionFieldMap hgen).hom.toAlgebra
      Algebra.IsSeparable X.functionField Y.functionField)
  (hy : IsClosed {y})

include κ hy in
omit [IsIntegral X] [IsIntegral Y] [Y.Over (Spec (.of κ))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of κ))] in
/-- Over a perfect field `κ`, the residue field of `𝒪_{X,f(y)}` at a closed point `y` is perfect:
it is a finite extension of `κ`. -/
theorem perfectField_residueField [PerfectField κ] :
    PerfectField (X.presheaf.stalk (f y) ⧸ maximalIdeal (X.presheaf.stalk (f y))) := by
  have : Smooth (X ↘ Spec (.of κ)) := SmoothOfRelativeDimension.smooth 1 _
  let : Algebra κ (X.presheaf.stalk (f y) ⧸ maximalIdeal (X.presheaf.stalk (f y))) :=
    ((X ↘ Spec (.of κ)).residueFieldAlgebraMap (f y)).toAlgebra
  have : Module.Finite κ (X.presheaf.stalk (f y) ⧸ maximalIdeal (X.presheaf.stalk (f y))) :=
    (X ↘ Spec (.of κ)).finite_residueField_of_isClosed (f y) (f.isClosed_singleton_apply hy)
  exact Algebra.IsAlgebraic.perfectField κ

include hsep hy in
/-- Over a perfect field `κ`, at a closed point `y` the residue field of `𝔓_y` is separable over
the residue field of `𝒪_{X,f(y)}`. -/
theorem isSeparable_residueField_curvePrime [PerfectField κ] :
    haveI := isMaximal_curvePrime κ f hgen hsep y hy
    haveI := curvePrime_liesOver κ f y
    Algebra.IsSeparable (X.presheaf.stalk (f y) ⧸ maximalIdeal (X.presheaf.stalk (f y)))
      (curveSemilocalRing f y ⧸ curvePrime f y) := by
  have := isMaximal_curvePrime κ f hgen hsep y hy
  have := curvePrime_liesOver κ f y
  have := finite_curveSemilocalRing κ f hgen hsep y
  have := perfectField_residueField κ f y hy
  have : Module.Finite (X.presheaf.stalk (f y) ⧸ maximalIdeal (X.presheaf.stalk (f y)))
      (curveSemilocalRing f y ⧸ curvePrime f y) :=
    module_finite_of_liesOver (curvePrime f y) (maximalIdeal (X.presheaf.stalk (f y)))
  have : Algebra.IsAlgebraic (X.presheaf.stalk (f y) ⧸ maximalIdeal (X.presheaf.stalk (f y)))
      (curveSemilocalRing f y ⧸ curvePrime f y) := Algebra.IsIntegral.isAlgebraic
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end Residue

open Langlands.CommutativeAlgebra.TameDifferent in
/-- **The tame different** (Serre, *Local Fields*, III §6, Prop. 13): at a closed point `y` whose
ramification index is invertible in the perfect field `κ`, the local different exponent of a
finite separable morphism of smooth proper curves is `e_y - 1`. -/
theorem tameCurveDifferentStatement : TameCurveDifferentStatement.{u} := by
  intro κ _ _ X Y _ _ _ _ _ _ _ _ _ _ f _ _ hgen hsep y he
  obtain ⟨y, hy⟩ := y
  change IsClosed {y} at hy
  dsimp only at he ⊢
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of κ))
  have := isDedekindDomain_curveSemilocalRing κ f hgen hsep y
  have := isTorsionFree_curveSemilocalRing f hgen y
  have := finite_curveSemilocalRing κ f hgen hsep y
  have := isDedekindDomain_stalk κ (f y)
  have := isMaximal_curvePrime κ f hgen hsep y hy
  have := curvePrime_liesOver κ f y
  have := isSeparable_residueField_curvePrime κ f y hgen hsep hy
  let := (f.functionFieldMap hgen).hom.toAlgebra
  have := isScalarTower_functionField f hgen y
  have : Algebra.IsSeparable X.functionField Y.functionField := hsep
  have : FiniteDimensional X.functionField Y.functionField := f.finiteDimensional_functionField hgen
  have := integralClosure.isFractionRing_of_finite_extension (A := X.presheaf.stalk (f y))
    X.functionField Y.functionField
  have hA := maximalIdeal_stalk_apply_ne_bot κ f y hy
  have hram := ramificationIndex_eq_ramificationIdx κ f hgen hsep y hy
  rw [hram] at he
  have he' : (((curvePrime f y).ramificationIdx (X.presheaf.stalk (f y)) : ℕ) :
      X.presheaf.stalk (f y) ⧸ maximalIdeal (X.presheaf.stalk (f y))) ≠ 0 :=
    natCast_ne_zero_residueField κ f y _ (by exact_mod_cast he)
  have he0 : (curvePrime f y).ramificationIdx (X.presheaf.stalk (f y)) ≠ 0 := by
    rintro h
    rw [h, Nat.cast_zero] at he'
    exact he' rfl
  have hcount := count_normalizedFactors_differentIdeal_of_isSeparable (X.presheaf.stalk (f y))
    X.functionField Y.functionField (curvePrime f y) hA he'
  rw [curveDifferentExponent_eq_count κ f hgen hsep y hy, hcount, hram]
  omega

end Langlands.Henniart.Laumon
