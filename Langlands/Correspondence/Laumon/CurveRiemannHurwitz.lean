import Langlands.MathlibBase
import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
import WeilConjectures.AlgebraicGeometry.Curve.DivisorDegree
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch

/-!
# The different divisor of a finite separable map of curves and the Riemann–Hurwitz formula

For a finite morphism `f : Y ⟶ X` of smooth proper geometrically connected curves over a perfect
field `κ`, whose extension of function fields `κ(Y)/κ(X)` is separable, this file defines the
local different exponent `δ_y` at a point `y` of `Y` and the effective different divisor
`D_f = ∑_y δ_y [y]`, and states:

* `CurveDifferentialsDifferentStatement`: the canonical maps
  `𝒪_{Y,y} ⊗ Ω_{𝒪_{X,f(y)}/κ} → Ω_{𝒪_{Y,y}/κ}` are injective, their cokernels vanish outside
  finitely many points and have length `δ_y` at a closed point `y`, and
  `Ω¹_{Y/κ} ≅ f^*Ω¹_{X/κ} ⊗ 𝒪_Y(D_f)` (Serre, *Local Fields*, III §§3–4 and §7, Prop. 14;
  Raynaud, Séminaire Bourbaki 286, §4, Lemme 1);
* `TameCurveDifferentStatement`: `δ_y = e_y - 1` when the ramification index `e_y` is invertible
  in `κ` (Serre, III §6, Prop. 13);
* `CurveRiemannHurwitzDifferentStatement`: `2g(Y) - 2 = n (2g(X) - 2) + ∑_y [κ(y) : κ] δ_y`
  with `n = [κ(Y) : κ(X)]`, with its algebraically closed form (the Hurwitz formula of Raynaud,
  §4, Lemme 1, whose printed sign of the different term is corrected in the Markdown) and its
  tame form (with Serre, III §6, Prop. 13).

The exponent `δ_y` is the exponent at `y` of Mathlib's `differentIdeal` of the integral closure
of the local ring `𝒪_{X,f(y)}` in `κ(Y)` over `𝒪_{X,f(y)}`; by Serre III §4, Props. 9–10, it is
the exponent of the different of the completed local extension at `y`.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace Langlands.Henniart.Laumon

section Local

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)

/-- The ring map `𝒪_{X,f(y)} → κ(Y)` through the local ring `𝒪_{Y,y}`, as an algebra
structure. -/
abbrev curveStalkFunctionFieldAlgebra (y : Y) : Algebra (X.presheaf.stalk (f y)) Y.functionField :=
  ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (f.stalkMap y).hom).toAlgebra

attribute [local instance] curveStalkFunctionFieldAlgebra

/-- The integral closure of the local ring `𝒪_{X,f(y)}` in the function field `κ(Y)`. For a
finite generically separable morphism of smooth curves and a closed point `y` it is the
semilocal ring of `Y` along the fibre of `f` through `y`, a Dedekind domain whose maximal ideals
correspond to the points of that fibre; at the generic point it is `κ(Y)`. -/
abbrev curveSemilocalRing (y : Y) : Subalgebra (X.presheaf.stalk (f y)) Y.functionField :=
  integralClosure (X.presheaf.stalk (f y)) Y.functionField

variable [IsLocallyNoetherian Y]

open Classical in
/-- **The local different exponent** `δ_y` of `f` at a point `y` of `Y`. Let `A = 𝒪_{X,f(y)}`
and let `B` be the integral closure of `A` in `κ(Y)` (`curveSemilocalRing`). Then `δ_y` is the
order of vanishing at `y` (`AlgebraicGeometry.Scheme.ord`, the normalized valuation of `y`) of
Mathlib's different ideal `differentIdeal A B`: the least order at `y` of a nonzero element of
the different ideal. The value is `0` when `B` is not a Dedekind domain or not torsion-free over
`A`, the conditions under which `differentIdeal` is defined; both hold at every point when `f`
is a finite generically separable morphism of smooth curves. -/
def curveDifferentExponent (y : Y) : ℕ :=
  if h : IsDedekindDomain (curveSemilocalRing f y) ∧
      Module.IsTorsionFree (X.presheaf.stalk (f y)) (curveSemilocalRing f y) then
    haveI := h.1
    haveI := h.2
    (sInf ((fun d : curveSemilocalRing f y ↦ Y.ord (d : Y.functionField) y) ''
      {d | d ∈ differentIdeal (X.presheaf.stalk (f y)) (curveSemilocalRing f y) ∧ d ≠ 0})).toNat
  else 0

open Classical in
/-- **The different divisor** `D_f = ∑_y δ_y [y]` of `f`, an effective divisor on `Y` given as a
finitely supported function on the closed points (the encoding of
`AlgebraicGeometry.Scheme.Divisor.idealSheaf`), with coefficient `curveDifferentExponent f y`
at a closed point `y`. The value is `0` when infinitely many of these exponents are nonzero; for
a finite generically separable morphism of smooth curves only finitely many are
(`CurveDifferentialsDifferentStatement`). -/
def curveDifferent : closedPoints Y →₀ ℕ :=
  if h : (Function.support fun y : closedPoints Y ↦ curveDifferentExponent f y.1).Finite then
    Finsupp.ofSupportFinite (fun y : closedPoints Y ↦ curveDifferentExponent f y.1) h
  else 0

end Local

section Differentials

variable (κ : Type u) [Field κ]

/-- The `κ`-algebra structure of the local ring `𝒪_{X,x}` of a `κ`-scheme `X`: the structure map
`κ → Γ(X, 𝒪_X)` (`AlgebraicGeometry.Scheme.globalSectionsRingHom`) followed by the germ at
`x`. -/
abbrev stalkAlgebraOver (X : Scheme.{u}) [X.Over (Spec (.of κ))] (x : X) :
    Algebra κ (X.presheaf.stalk x) :=
  ((X.presheaf.Γgerm x).hom.comp (Scheme.globalSectionsRingHom κ (X := X))).toAlgebra

variable {X Y : Scheme.{u}} [X.Over (Spec (.of κ))] (f : Y ⟶ X)

/-- The canonical map `𝒪_{Y,y} ⊗_{𝒪_{X,f(y)}} Ω_{𝒪_{X,f(y)}/κ} → Ω_{𝒪_{Y,y}/κ}`
(`KaehlerDifferential.mapBaseChange`), the stalk at `y` of `f^*Ω¹_{X/κ} → Ω¹_{Y/κ}`, is
injective. Here `𝒪_{Y,y}` is an `𝒪_{X,f(y)}`-algebra by the stalk map of `f` and a `κ`-algebra
through `𝒪_{X,f(y)}`; when `f` is a morphism over `κ` this is the `κ`-algebra structure of `Y`. -/
def IsStalkDifferentialsMapInjective (y : Y) : Prop :=
  letI : Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) := (f.stalkMap y).hom.toAlgebra
  letI : Algebra κ (X.presheaf.stalk (f y)) := stalkAlgebraOver κ X (f y)
  letI : Algebra κ (Y.presheaf.stalk y) :=
    ((algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)).comp
      (algebraMap κ (X.presheaf.stalk (f y)))).toAlgebra
  haveI : IsScalarTower κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Function.Injective
    (KaehlerDifferential.mapBaseChange κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y))

/-- The length, as an `𝒪_{Y,y}`-module, of the cokernel of the canonical map
`𝒪_{Y,y} ⊗_{𝒪_{X,f(y)}} Ω_{𝒪_{X,f(y)}/κ} → Ω_{𝒪_{Y,y}/κ}`
(`KaehlerDifferential.mapBaseChange`), with the algebra structures of
`IsStalkDifferentialsMapInjective`. This cokernel is the stalk at `y` of the cokernel of
`f^*Ω¹_{X/κ} → Ω¹_{Y/κ}`; by the exact sequence `KaehlerDifferential.exact_mapBaseChange_map` it
is `Ω_{𝒪_{Y,y}/𝒪_{X,f(y)}}`. -/
def stalkDifferentialsCokernelLength (y : Y) : ℕ∞ :=
  letI : Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) := (f.stalkMap y).hom.toAlgebra
  letI : Algebra κ (X.presheaf.stalk (f y)) := stalkAlgebraOver κ X (f y)
  letI : Algebra κ (Y.presheaf.stalk y) :=
    ((algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)).comp
      (algebraMap κ (X.presheaf.stalk (f y)))).toAlgebra
  haveI : IsScalarTower κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Module.length (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄κ] ⧸ LinearMap.range
    (KaehlerDifferential.mapBaseChange κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)))

end Differentials

/-- **Differentials and the different** (Serre, *Local Fields*, III §7, Prop. 14, pp. 59–60, with
III §4, Props. 9–10, pp. 51–52; Raynaud, Séminaire Bourbaki 286, §4, Lemme 1, pp. 133–134).
Let `κ` be a perfect field, `X` and `Y` smooth proper geometrically connected curves over `κ`
and `f : Y ⟶ X` a finite morphism over `κ` mapping the generic point to the generic point, with
`κ(Y)/κ(X)` separable. Then:

1. at every point `y` of `Y` the canonical map
   `𝒪_{Y,y} ⊗ Ω_{𝒪_{X,f(y)}/κ} → Ω_{𝒪_{Y,y}/κ}` is injective;
2. its cokernel is nonzero at only finitely many points `y`;
3. at a closed point `y` the cokernel has length `δ_y = curveDifferentExponent f y`;
4. the coefficient of the different divisor `D_f = curveDifferent f` at a closed point `y` is
   `δ_y`;
5. `Ω¹_{Y/κ} ≅ f^*Ω¹_{X/κ} ⊗ 𝒪_Y(D_f)`, where `𝒪_Y(D_f)` is the dual of the ideal sheaf
   `AlgebraicGeometry.Scheme.Divisor.idealSheaf (curveDifferent f)`. -/
def CurveDifferentialsDifferentStatement : Prop :=
  ∀ (κ : Type u) [Field κ] [PerfectField κ] (X Y : Scheme.{u})
    [X.Over (Spec (.of κ))] [Y.Over (Spec (.of κ))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))] [IsProper (X ↘ Spec (.of κ))]
    [GeometricallyConnected (X ↘ Spec (.of κ))] [IsIntegral X]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of κ))] [IsProper (Y ↘ Spec (.of κ))]
    [GeometricallyConnected (Y ↘ Spec (.of κ))] [IsIntegral Y]
    (f : Y ⟶ X) [f.IsOver (Spec (.of κ))] [IsFinite f]
    (hgen : f (genericPoint Y) = genericPoint X)
    (_ : letI := (f.functionFieldMap hgen).hom.toAlgebra
      Algebra.IsSeparable X.functionField Y.functionField),
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of κ))
    (∀ y : Y, IsStalkDifferentialsMapInjective κ f y) ∧
    {y : Y | stalkDifferentialsCokernelLength κ f y ≠ 0}.Finite ∧
    (∀ y : closedPoints Y,
      stalkDifferentialsCokernelLength κ f y.1 = curveDifferentExponent f y.1) ∧
    (∀ y : closedPoints Y, curveDifferent f y = curveDifferentExponent f y.1) ∧
    Nonempty ((Y ↘ Spec (.of κ)).relativeDifferentials ≅
      (Scheme.Modules.pullback f).obj (X ↘ Spec (.of κ)).relativeDifferentials ⊗
        (Scheme.Divisor.idealSheaf (curveDifferent f)).toModulesᵛ)

/-- **The tame different** (Serre, *Local Fields*, III §6, Prop. 13, p. 58; for Galois completed
extensions also IV §1, Prop. 4, p. 64, and IV §2, Prop. 7, Cor. 1, p. 67). In the setting of
`CurveDifferentialsDifferentStatement`, let `y` be a closed point of `Y` whose ramification index
`e_y` (`AlgebraicGeometry.Scheme.Hom.ramificationIndex`) is invertible in `κ`, that is, prime to
the characteristic of `κ`. Then `δ_y = e_y - 1`. -/
def TameCurveDifferentStatement : Prop :=
  ∀ (κ : Type u) [Field κ] [PerfectField κ] (X Y : Scheme.{u})
    [X.Over (Spec (.of κ))] [Y.Over (Spec (.of κ))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))] [IsProper (X ↘ Spec (.of κ))]
    [GeometricallyConnected (X ↘ Spec (.of κ))] [IsIntegral X]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of κ))] [IsProper (Y ↘ Spec (.of κ))]
    [GeometricallyConnected (Y ↘ Spec (.of κ))] [IsIntegral Y]
    (f : Y ⟶ X) [f.IsOver (Spec (.of κ))] [IsFinite f]
    (hgen : f (genericPoint Y) = genericPoint X)
    (_ : letI := (f.functionFieldMap hgen).hom.toAlgebra
      Algebra.IsSeparable X.functionField Y.functionField),
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of κ))
    ∀ y : closedPoints Y, ((f.ramificationIndex y.1 : ℤ) : κ) ≠ 0 →
      (curveDifferentExponent f y.1 : ℤ) = f.ramificationIndex y.1 - 1

/-- **The Riemann–Hurwitz formula** (Raynaud, Séminaire Bourbaki 286, §4, Lemme 1, pp. 133–134,
whose formula `χ(C') = [K' : K] χ(C) + d(K' : K)` on p. 134 needs a minus sign before
`d(K' : K)` under his convention `χ = 2 - 2g`; the tame form follows with Serre, *Local Fields*,
III §6, Prop. 13, p. 58). The tame form is applied to coverings of `𝔾_m` tame at `0` and `∞`
in the sense of Katz, *Local-to-global extensions*, (1.1.2)–(1.1.3), pp. 71–72, the setting of
his §§1.2–1.3 and Prop. (1.4.2) that lead to the canonical extension. In the setting of
`CurveDifferentialsDifferentStatement`, let `n = [κ(Y) : κ(X)]` and let `g(X)`, `g(Y)` be the
genera `dim_κ H⁰(Ω¹)` (`AlgebraicGeometry.Scheme.Hom.genus`). Then

1. `2g(Y) - 2 = n (2g(X) - 2) + ∑_y [κ(y) : κ] δ_y`, the sum over the closed points `y` of `Y`
   with the coefficients `δ_y` of `D_f = curveDifferent f` and the residue degrees
   `[κ(y) : κ]` (`AlgebraicGeometry.Scheme.Hom.degreeOver`);
2. if `κ` is algebraically closed, `2g(Y) - 2 = n (2g(X) - 2) + deg D_f`, with the degree
   `AlgebraicGeometry.Scheme.Divisor.degree`;
3. if every closed point `y` of `Y` has ramification index `e_y` invertible in `κ`, then
   `2g(Y) - 2 = n (2g(X) - 2) + ∑_y [κ(y) : κ] (e_y - 1)`. -/
def CurveRiemannHurwitzDifferentStatement : Prop :=
  ∀ (κ : Type u) [Field κ] [PerfectField κ] (X Y : Scheme.{u})
    [X.Over (Spec (.of κ))] [Y.Over (Spec (.of κ))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))] [IsProper (X ↘ Spec (.of κ))]
    [GeometricallyConnected (X ↘ Spec (.of κ))] [IsIntegral X]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of κ))] [IsProper (Y ↘ Spec (.of κ))]
    [GeometricallyConnected (Y ↘ Spec (.of κ))] [IsIntegral Y]
    (f : Y ⟶ X) [f.IsOver (Spec (.of κ))] [IsFinite f]
    (hgen : f (genericPoint Y) = genericPoint X)
    (_ : letI := (f.functionFieldMap hgen).hom.toAlgebra
      Algebra.IsSeparable X.functionField Y.functionField),
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of κ))
    letI := (f.functionFieldMap hgen).hom.toAlgebra
    let n : ℤ := Module.finrank X.functionField Y.functionField
    let gX : ℤ := (X ↘ Spec (.of κ)).genus
    let gY : ℤ := (Y ↘ Spec (.of κ)).genus
    (2 * gY - 2 = n * (2 * gX - 2) +
      (curveDifferent f).sum fun y d ↦ (d : ℤ) * (Y ↘ Spec (.of κ)).degreeOver y.1) ∧
    (IsAlgClosed κ → 2 * gY - 2 = n * (2 * gX - 2) +
      Scheme.Divisor.degree Y ((curveDifferent f).mapRange Nat.cast Nat.cast_zero)) ∧
    ((∀ y : closedPoints Y, ((f.ramificationIndex y.1 : ℤ) : κ) ≠ 0) →
      2 * gY - 2 = n * (2 * gX - 2) + ∑ᶠ y : closedPoints Y,
        (f.ramificationIndex y.1 - 1) * ((Y ↘ Spec (.of κ)).degreeOver y.1 : ℤ))

end Langlands.Henniart.Laumon
