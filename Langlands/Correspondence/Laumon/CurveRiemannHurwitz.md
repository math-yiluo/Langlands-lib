# The different divisor of a finite separable map of curves and the Riemann–Hurwitz formula

Module `Langlands.Correspondence.Laumon.CurveRiemannHurwitz`, namespace
`Langlands.Henniart.Laumon`. For a finite, generically separable morphism `f : Y → X` of
smooth, projective, geometrically connected curves over a perfect field `κ`, the module defines
the local different exponents `δ_y` and the different divisor `D_f = Σ_y δ_y [y]`, and states
three propositions:

- `CurveDifferentialsDifferentStatement`: the map `f*Ω¹_X → Ω¹_Y` is injective, its cokernel is
  supported at finitely many points, its length at `y` is `δ_y`, and
  `ω_Y ≅ f*ω_X ⊗ 𝒪_Y(D_f)`;
- `TameCurveDifferentStatement`: `δ_y = e_y − 1` when the ramification index `e_y` is prime to
  the characteristic;
- `CurveRiemannHurwitzDifferentStatement`:
  `2g(Y) − 2 = n (2g(X) − 2) + Σ_y [κ(y) : κ] δ_y` with `n = [κ(Y) : κ(X)]`, together with its
  algebraically closed form and its tame form.

The file states these propositions and does not prove them. The module imports
`Langlands.MathlibBase` (never `Mathlib` whole) and three modules of weil-conjectures:
`WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`,
`WeilConjectures.AlgebraicGeometry.Curve.DivisorDegree` and
`WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`.

## Declarations

| Declaration | Kind | Content |
|---|---|---|
| `curveStalkFunctionFieldAlgebra f y` | algebra structure (`abbrev`) | `𝒪_{X,f(y)} → 𝒪_{Y,y} → κ(Y)`, the stalk map of `f` followed by Mathlib's map from a stalk to the function field |
| `curveSemilocalRing f y` | subalgebra (`abbrev`) | the integral closure of `𝒪_{X,f(y)}` in `κ(Y)` |
| `curveDifferentExponent f y` | `ℕ` | the local different exponent `δ_y` |
| `curveDifferent f` | `closedPoints Y →₀ ℕ` | the different divisor `D_f` |
| `stalkAlgebraOver κ X x` | algebra structure (`abbrev`) | the `κ`-algebra structure of `𝒪_{X,x}` |
| `IsStalkDifferentialsMapInjective κ f y` | `Prop` | injectivity of `𝒪_{Y,y} ⊗ Ω_{𝒪_{X,f(y)}/κ} → Ω_{𝒪_{Y,y}/κ}` |
| `stalkDifferentialsCokernelLength κ f y` | `ℕ∞` | the length of the cokernel of that map |
| `CurveDifferentialsDifferentStatement` | `Prop` | differentials and the different |
| `TameCurveDifferentStatement` | `Prop` | the tame different |
| `CurveRiemannHurwitzDifferentStatement` | `Prop` | the Riemann–Hurwitz formula |

The names `curveDifferent`, `CurveDifferentialsDifferentStatement`,
`TameCurveDifferentStatement` and `CurveRiemannHurwitzDifferentStatement` are those of the
two `CurveRiemannHurwitz` rows of §4.2 of the design note
[Laumon's local Fourier bijection on weil-conjectures](../../../notes/henniart/laumon-local-fourier-weil-conjectures-design.md).
The exponent `δ_y` of that note is `curveDifferentExponent f y`. The two maps of Kähler
differentials are packaged as `IsStalkDifferentialsMapInjective` and
`stalkDifferentialsCokernelLength`, so that the three statements need no local instances. The
three algebra structures and the semilocal ring are auxiliary.

## The setting of the three statements

All three propositions quantify over the same data, written out in each of them:

- a field `κ : Type u` with `[PerfectField κ]`;
- schemes `X Y : Scheme.{u}` over `Spec κ` (`[X.Over (Spec (.of κ))]`), each with
  `[SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))]`, `[IsProper (X ↘ Spec (.of κ))]`,
  `[GeometricallyConnected (X ↘ Spec (.of κ))]` and `[IsIntegral X]`;
- a morphism `f : Y ⟶ X` with `[f.IsOver (Spec (.of κ))]` and `[IsFinite f]`;
- `hgen : f (genericPoint Y) = genericPoint X`;
- separability of `κ(Y)` over `κ(X)`: `Algebra.IsSeparable X.functionField Y.functionField`
  for the algebra structure `(f.functionFieldMap hgen).hom.toAlgebra`.

Inside each statement `IsLocallyNoetherian Y` is installed by Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` applied to `Y ↘ Spec (.of κ)`.
`AlgebraicGeometry.Scheme.ord` and `AlgebraicGeometry.Scheme.Hom.ramificationIndex` need this
instance. It is a proposition, so how it is found does not change what the statements say.

**Smooth projective geometrically connected curves.** A curve is encoded as in the curve
declarations of weil-conjectures listed in §3.6 of the design note. `X ↘ Spec κ` is smooth of
relative dimension one and proper. *Projective* is spelled `IsProper`: a projective scheme over
a field is proper. Conversely, a separated scheme of finite type over a field of dimension at
most one has an ample invertible module (Stacks Project, Varieties, Lemma 0A25), so a proper
curve is projective. The curve results of §3.6 that need a complete curve assume properness, not
projectivity: `degree_relativeDifferentials`, `genus_eq_arithmeticGenus`,
`degree_dual_toModules_idealSheaf` and `degree_pullback_eq_finrank_functionField_mul` assume
`IsProper` together with smoothness of relative dimension one. The local declarations assume
less: `AlgebraicGeometry.Scheme.Hom.ramificationIndex` only a locally Noetherian integral source,
`AlgebraicGeometry.Scheme.Divisor.pullback` in addition a finite morphism, and
`isDiscreteValuationRing_stalk_of_isClosed` only smoothness of relative dimension one.
*Geometrically connected* is Mathlib's `AlgebraicGeometry.GeometricallyConnected`:
`X ×_κ Spec K` is connected for every field `K` over `κ`. Smoothness makes `X ↘ Spec κ`
geometrically reduced (an instance found by `inferInstance`), and weil-conjectures' instance
`AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyConnected` then gives
`GlobalSectionsBijective κ X`, that is `H⁰(X, 𝒪_X) = κ`. In the setting above,
`inferInstance` finds `GlobalSectionsBijective κ X` once
`AlgebraicGeometry.SmoothOfRelativeDimension.smooth` is available. This is the hypothesis of
`AlgebraicGeometry.Scheme.degree_relativeDifferentials` (`deg Ω¹ = 2g − 2`) and of Riemann–Roch
in the form `χ(𝒪) = 1 − g`. `IsIntegral X` follows from the other hypotheses: a smooth scheme
over a field is normal, and a connected normal Noetherian scheme is integral. It is a hypothesis
because the function field, the order of vanishing and the ramification index need it as an
instance; the curve modules of weil-conjectures assume it in the same way.

**The morphism.** `hgen` and separability together say that `f` is generically separable: the
generic point of `Y` maps to that of `X`, and the induced extension of function fields is
separable. The extension is `AlgebraicGeometry.Scheme.Hom.functionFieldMap`, the stalk map of
`f` at the generic point. For a finite morphism of curves `hgen` always holds, because the image
of `f` is closed, irreducible and of dimension one. It is a hypothesis because the field map is
defined from it. The algebra structure does not depend on the proof of `hgen`. In particular it
is the algebra structure `(f.functionFieldMap f.apply_genericPoint_of_flat).hom.toAlgebra` of
`AlgebraicGeometry.Scheme.Divisor.degree_pullback_eq_finrank_functionField_mul`. A finite
morphism `f` of smooth curves with `hgen` is flat. At a closed point `y` of `Y`, the point
`f(y)` is closed because `f` is finite, so the local ring `𝒪_{X,f(y)}` is a discrete valuation
ring. The local ring `𝒪_{Y,y}` embeds in `κ(Y)`, and
`𝒪_{X,f(y)} → κ(Y)` is injective by `hgen`, so `𝒪_{Y,y}` is a torsion-free, hence flat,
`𝒪_{X,f(y)}`-module. At the generic point `𝒪_{X,f(y)}` is the field `κ(X)`.
`n = [κ(Y) : κ(X)]` is `Module.finrank X.functionField Y.functionField` for this algebra
structure.

**The genus.** `g(X)` is `(X ↘ Spec (.of κ)).genus`
(`AlgebraicGeometry.Scheme.Hom.genus`), the dimension over `κ` of `H⁰(X, Ω¹_{X/κ})`. On a smooth
proper curve it equals the arithmetic genus `AlgebraicGeometry.Scheme.arithmeticGenus κ X`,
`dim_κ H¹(X, 𝒪_X)`, by `AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`. The arithmetic genus
does not change under extension of the ground field
(`AlgebraicGeometry.Scheme.arithmeticGenus_pullback`). With `H⁰(𝒪) = κ`,
`AlgebraicGeometry.Scheme.degree_relativeDifferentials` gives `deg Ω¹_{X/κ} = 2g − 2`, where the
degree of a line bundle is `χ(ℒ) − χ(𝒪)` (`AlgebraicGeometry.Scheme.Modules.degree`).

**Points, divisors and degrees.** Divisors on `Y` are weil-conjectures'
`AlgebraicGeometry.Scheme.Divisor Y = closedPoints Y →₀ ℤ`. An effective divisor is a function
`closedPoints Y →₀ ℕ`, the input of `AlgebraicGeometry.Scheme.Divisor.idealSheaf`, which gives
the ideal sheaf `𝒪_Y(−E) = ∏_P 𝓘_P^{n_P}`. Its dual `(Divisor.idealSheaf E).toModulesᵛ` is
`𝒪_Y(E)`. `AlgebraicGeometry.Scheme.Divisor.degree_dual_toModules_idealSheaf` gives
`deg 𝒪_Y(E) = Σ_P n_P [κ(P) : κ]`. The residue degree `[κ(P) : κ]` is
`(Y ↘ Spec (.of κ)).degreeOver P` (`AlgebraicGeometry.Scheme.Hom.degreeOver`).
`AlgebraicGeometry.Scheme.Divisor.degree` is the unweighted degree `Σ_P n_P`, which is the
weighted one over an algebraically closed field. The ramification index `e_y` is
`f.ramificationIndex y` (`AlgebraicGeometry.Scheme.Hom.ramificationIndex`): the order at `y` of
the image of a generator of the maximal ideal of `𝒪_{X,f(y)}`. The pullback
`AlgebraicGeometry.Scheme.Divisor.pullback` of divisors uses these indices, and over an
algebraically closed field `degree_pullback_eq_finrank_functionField_mul` gives
`deg f*D = n deg D`. The statements do not mention divisor pullback. Its degree formula, the
canonical degree, the divisor degree and the genus comparisons above are inputs for the proof of
`CurveRiemannHurwitzDifferentStatement` from `CurveDifferentialsDifferentStatement`.

## The definitions

**The semilocal ring.** For a point `y` of `Y`, let `x = f(y)` and `A = 𝒪_{X,x}` (Mathlib's
`X.presheaf.stalk x`). `curveStalkFunctionFieldAlgebra f y` makes `κ(Y)` an `A`-algebra through
the stalk map `A → 𝒪_{Y,y}` of `f` and the map `𝒪_{Y,y} → κ(Y)`. `curveSemilocalRing f y` is
Mathlib's `integralClosure A κ(Y)` for this structure. For a finite generically separable `f`
between smooth curves and a closed point `y`, `A` is a discrete valuation ring
(`AlgebraicGeometry.Scheme.isDiscreteValuationRing_stalk_of_isClosed`), so `B` is Serre's
integral closure of the Dedekind domain `A` in the finite separable extension `κ(Y)` of
`κ(X) = Frac A`. Its maximal ideals are the primes `𝔓_{y'} = B ∩ 𝔪_{y'}` for the points `y'` of
the fibre over `x`, and `B_{𝔓_{y'}} = 𝒪_{Y,y'}`. For `y` the generic point, `B = κ(Y)`.

**`curveDifferentExponent f y`.** Mathlib's `differentIdeal A B`
(`Mathlib/RingTheory/DedekindDomain/Different.lean`) is the preimage in `B` of
`1 / traceDual A (FractionRing A) 1`, the inverse of the codifferent
`B* = {z : Tr(zB) ⊆ A}`. This is Serre's definition of the different `𝔇_{B/A}` (III §3,
p. 50). It needs the instances `IsDomain A` (Mathlib's instance for the stalks of an integral
scheme), `IsDedekindDomain B` and `Module.IsTorsionFree A B`. The definition tests the last two:

```text
curveDifferentExponent f y =
  if IsDedekindDomain B ∧ Module.IsTorsionFree A B then
    (sInf { Y.ord d y | d ∈ differentIdeal A B, d ≠ 0 }).toNat
  else 0
```

Here `Y.ord d y` is Mathlib's order of vanishing `AlgebraicGeometry.Scheme.ord` at `y` of
`d ∈ B ⊆ κ(Y)`. At a closed point of a smooth curve it is the normalized valuation of the
discrete valuation ring `𝒪_{Y,y}`, and at the generic point it is `0`. In the setting of the
statements both tested conditions hold at every point. `B` is a Dedekind domain, being the
integral closure of a Dedekind domain in a finite separable extension of its fraction field (a
field when `y` is generic). `A → κ(Y)` is injective because `f` maps the generic point to the
generic point, so `B ⊆ κ(Y)` is torsion-free over `A`. The different ideal is nonzero by
separability and `B ⊆ 𝒪_{Y,y}`, so the orders form a nonempty set of natural numbers. Its least
element is the exponent of `𝔓_y` in `𝔇_{B/A}`. If `𝔇_{B/A} = ∏ 𝔓^{m_𝔓}`, every element has
order at least `m_{𝔓_y}` at `y`, and an element of `𝔇_{B/A}` outside `𝔓_y^{m+1}` has order
exactly `m = m_{𝔓_y}`. So `curveDifferentExponent f y` is the exponent of `𝔓_y` in the
different of `B/A`. At the generic point it is `0`.

The design note and Serre take `δ_y` to be the exponent of the different of the completed
local extension `𝒪̂_{Y,y} / 𝒪̂_{X,x}`, measured by the normalized valuation of `y`. The two
agree: the different is compatible with localization at multiplicative subsets of `A` (Serre
III §4, Prop. 9, p. 51), and "the different is preserved by completion": the exponent of `𝔓` in
`𝔇_{B/A}` is the exponent of `𝔓B̂_𝔓` in the different of `B̂_𝔓` over `Â_𝔭` (Serre III §4,
Prop. 10, p. 52). The definition uses the semilocal Dedekind ring, to which Mathlib's
`differentIdeal` applies directly, without completing.

**`curveDifferent f`.** The function `y ↦ curveDifferentExponent f y` on `closedPoints Y`, as an
element of `closedPoints Y →₀ ℕ` (Mathlib's `Finsupp.ofSupportFinite`) when its support is
finite, and `0` otherwise. In the setting of the statements the support is finite: it consists
of the ramified points. Conjunct 4 of `CurveDifferentialsDifferentStatement` asserts that the
coefficients are the `δ_y`. The value is an effective divisor in the encoding of
`Divisor.idealSheaf`. As a divisor in `AlgebraicGeometry.Scheme.Divisor Y` it is
`(curveDifferent f).mapRange Nat.cast Nat.cast_zero`.

**The maps of differentials.** `stalkAlgebraOver κ X x` is the `κ`-algebra structure of
`𝒪_{X,x}` given by the structure map `κ → Γ(X, 𝒪_X)`
(`AlgebraicGeometry.Scheme.globalSectionsRingHom`) followed by the germ at `x`. In
`IsStalkDifferentialsMapInjective κ f y` and `stalkDifferentialsCokernelLength κ f y`, the local
ring `𝒪_{Y,y}` is an `𝒪_{X,f(y)}`-algebra by the stalk map of `f`. It is a `κ`-algebra through
`𝒪_{X,f(y)}`, so the scalar tower `κ → 𝒪_{X,f(y)} → 𝒪_{Y,y}` holds by definition. When `f` is
a morphism over `κ`, as in the statements, this is the `κ`-algebra structure that `𝒪_{Y,y}`
receives from `Y`. The map is Mathlib's `KaehlerDifferential.mapBaseChange κ 𝒪_{X,f(y)} 𝒪_{Y,y}
: 𝒪_{Y,y} ⊗ Ω[𝒪_{X,f(y)}⁄κ] → Ω[𝒪_{Y,y}⁄κ]`, `b ⊗ da ↦ b · d(f^♯ a)`. Kähler differentials
commute with localization, so it is the stalk at `y` of the canonical map `f*Ω¹_{X/κ} → Ω¹_{Y/κ}`,
and its cokernel is the stalk of the cokernel. The first predicate says that this map is
injective. The second is the `Module.length` over `𝒪_{Y,y}` of
`Ω[𝒪_{Y,y}⁄κ] ⧸ range`. By Mathlib's exact sequence
`KaehlerDifferential.exact_mapBaseChange_map` this cokernel is the relative module
`Ω[𝒪_{Y,y}⁄𝒪_{X,f(y)}]`. The statements express the map `f*Ω¹_X → Ω¹_Y` through its stalks,
which are maps of Mathlib's Kähler modules.

## The statements

**`CurveDifferentialsDifferentStatement`** (Serre, *Local Fields*, III §7, Prop. 14, pp. 59–60,
with III §4, Props. 9–10, pp. 51–52; Raynaud 1965, §4, Lemme 1, pp. 133–134). In the setting
above:

1. for every point `y` of `Y`, the map `𝒪_{Y,y} ⊗ Ω_{𝒪_{X,f(y)}/κ} → Ω_{𝒪_{Y,y}/κ}` is
   injective (`IsStalkDifferentialsMapInjective κ f y`);
2. the set of points `y` of `Y` at which its cokernel has nonzero length is finite;
3. at every closed point `y` the length of the cokernel is `δ_y`
   (`stalkDifferentialsCokernelLength κ f y = curveDifferentExponent f y`);
4. at every closed point `y`, `curveDifferent f y = curveDifferentExponent f y`;
5. there is an isomorphism of `𝒪_Y`-modules
   `Ω¹_{Y/κ} ≅ f*Ω¹_{X/κ} ⊗ 𝒪_Y(D_f)`, written
   `(Y ↘ Spec (.of κ)).relativeDifferentials ≅
   (Scheme.Modules.pullback f).obj (X ↘ Spec (.of κ)).relativeDifferentials ⊗
   (Scheme.Divisor.idealSheaf (curveDifferent f)).toModulesᵛ`.

Serre's Prop. 14 says that, for the integral closure `B` of a Dedekind domain `A` in a finite
separable extension with separable residue extensions, `Ω_A(B)` is generated by one element and
its annihilator is `𝔇_{B/A}`. The residue fields of closed points are finite extensions of the
perfect field `κ`, so the residue extensions are separable. Localizing `Ω_A(B) ≅ B / 𝔇_{B/A}`
at `𝔓_y` gives a module of length `δ_y` over `𝒪_{Y,y}`. Injectivity holds because both modules
in item 1 are free of rank one at closed points, and the map is an isomorphism over `κ(Y)` by
separability. Taking degrees in item 5 gives the Hurwitz formula used in Raynaud's Lemme 1
(p. 134). The printed sign of that formula is discussed under
`CurveRiemannHurwitzDifferentStatement` below.

**`TameCurveDifferentStatement`** (Serre III §6, Prop. 13, p. 58; for Galois completed
extensions also IV §1, Prop. 4, p. 64, and IV §2, Prop. 7, Cor. 1, p. 67). In the setting
above, let `y` be a closed point of `Y` whose
ramification index `e_y = f.ramificationIndex y` is invertible in `κ`, that is,
`((f.ramificationIndex y : ℤ) : κ) ≠ 0`. Then `(curveDifferentExponent f y : ℤ) = e_y − 1`.
Invertibility in `κ` is "prime to the characteristic" in every characteristic: in
characteristic zero every `e_y ≥ 1` qualifies, and in characteristic `p` the condition is
`p ∤ e_y`. The residue field of `X` at `f(y)` has the characteristic of `κ`, so this is Serre's
condition. Serre's Prop. 13 applies to the integral closure `B` of a Dedekind domain `A` in a
finite separable extension, at a prime of `B` with separable residue extension, with no Galois
hypothesis. It says that the exponent of the prime in `𝔇_{B/A}` is at least `e − 1`, with
equality if and only if `e` is prime to the residue characteristic. The residue extensions are
separable over a perfect field, so Prop. 13 gives the statement for every finite generically
separable `f`. When the completed extension at `y` is Galois, the equality can also be read
from the ramification groups (IV §1, Prop. 4, and IV §2, Prop. 7, Cor. 1): tameness means
`G_1 = 1`, and the exponent is `|G_0| − 1 = e − 1`. That computation does not cover the general
case, because the completed extension need not be Galois. For the map `t = u³` of the
projective line over `ℚ`, the completed extension at `u = 0` is `ℚ((u))/ℚ((t))`, with `e = 3`
and `δ = 2`, and it has no nontrivial automorphism, since `ℚ((u))` contains no primitive cube
root of unity.

**`CurveRiemannHurwitzDifferentStatement`** (the Riemann–Hurwitz formula; Raynaud 1965, §4,
Lemme 1, pp. 133–134, with the sign of the different term corrected as explained below; the
tame form by Serre III §6, Prop. 13, p. 58). In the setting above, with `n = [κ(Y) : κ(X)]`,
`g(X) = (X ↘ Spec κ).genus` and
`g(Y) = (Y ↘ Spec κ).genus` (all as integers):

1. `2g(Y) − 2 = n (2g(X) − 2) + Σ_y [κ(y) : κ] δ_y`, written with
   `(curveDifferent f).sum fun y d ↦ (d : ℤ) * (Y ↘ Spec (.of κ)).degreeOver y.1`;
2. if `κ` is algebraically closed, then
   `2g(Y) − 2 = n (2g(X) − 2) + deg D_f`, with
   `Scheme.Divisor.degree Y ((curveDifferent f).mapRange Nat.cast Nat.cast_zero)`;
3. if every closed point `y` of `Y` has `e_y` invertible in `κ`, then
   `2g(Y) − 2 = n (2g(X) − 2) + Σ_y [κ(y) : κ] (e_y − 1)`, the sum being the `finsum` over
   `closedPoints Y` of `(f.ramificationIndex y − 1) * degreeOver y`. Only finitely many terms
   are nonzero, namely those at ramified points.

Item 1 is the formula over every perfect field. Over an algebraically closed field every
residue degree is one, which gives item 2. Item 3 is item 1 combined with
`TameCurveDifferentStatement`. Item 1 is the degree of the isomorphism of item 5 of
`CurveDifferentialsDifferentStatement`, computed with `deg Ω¹ = 2g − 2` on both curves, with
`deg f*ℒ = n deg ℒ`, and with `deg 𝒪_Y(D_f) = Σ_y [κ(y) : κ] δ_y`
(`degree_dual_toModules_idealSheaf`). Over an algebraic closure of `κ`, the design note computes
these degrees with the divisor pullback and canonical-degree results of its §3.6. The base change
of the genus uses `arithmeticGenus_pullback`, and the points over `y` each carry the exponent
`δ_y`.

**The sign in Raynaud.** Raynaud works over an algebraically closed field `k` with
`χ(C) = 2 − 2g` (p. 129), and `d(K' : K)` is the degree of the discriminant of `K'` over `K`
(p. 131, Prop. 1(c)). Page 134 prints the Hurwitz formula as
`χ(C') = [K' : K] χ(C) + d(K' : K)`. With these conventions the different term must be
subtracted: `χ(C') = [K' : K] χ(C) − d(K' : K)`. The discriminant is the norm of the different
(Serre III §3, Prop. 6, p. 50). Over an algebraically closed field every residue degree is one,
so `d(K' : K) = deg D_f`. Subtracting both sides from zero gives
`−χ(C') = [K' : K](−χ(C)) + deg D_f`, that is
`2g(C') − 2 = [K' : K](2g(C) − 2) + deg D_f`, which is item 2. The map `u ↦ t = u²` of the
projective line over an algebraically closed field of characteristic `3` checks the sign. It has
degree `2` and is ramified exactly at `u = 0` and `u = ∞`, where `e = 2` is prime to `3`, so
`δ = 1` at both points and `deg D_f = 2`. Indeed `χ(ℙ¹) = 2 = 2 · 2 − 2`, whereas the printed
plus sign would give `2 · 2 + 2 = 6`.

**Where the tame form is applied.** Katz 1986 defines a finite étale covering of `𝔾_m` to be
tame at `0` if its pullback by the `N`-th power map, for some `N` invertible in the base field,
extends to a finite étale covering of the affine line ((1.1.2)–(1.1.3), pp. 71–72). His §§1.2–1.3
(pp. 73–76) treat the geometric monodromy of such coverings and the special coverings, those tame
at `0` whose geometric monodromy group has a unique `p`-Sylow subgroup. Prop. (1.4.2) (p. 79)
compares coverings of the affine line with `p`-group monodromy with those of the punctured formal
neighbourhood of `∞`. These results are the setting in which the design note (§4.3, row
`TameCovers`) applies item 3 to geometric coverings of `𝔾_m` tame at both ends, on the way to
Katz's canonical extension. The cited passages of Katz do not state the genus formula. Item 3
is the Riemann–Hurwitz formula of item 1 combined with Serre III §6, Prop. 13.

Each statement holds for all the data it quantifies over. No conjunct is assumed: the
different, the divisor and the cokernel lengths are defined from `f`, and the hypotheses contain
no different, no differential, no genus formula and no ramification datum.

## External declarations and their axioms

Each declaration below, and each declaration of this module, was checked with `#print axioms` in
the environment of the Library (Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
weil-conjectures `a25955cde4f85f67bef3149a6efc3efe20c22132`). Each reports exactly
`[propext, Classical.choice, Quot.sound]`, except `closedPoints`, which uses no axiom.

| Declaration | Library and module |
|---|---|
| `differentIdeal` | Mathlib, `Mathlib.RingTheory.DedekindDomain.Different` |
| `KaehlerDifferential.mapBaseChange` | Mathlib, `Mathlib.RingTheory.Kaehler.Basic` |
| `Module.length` | Mathlib, `Mathlib.RingTheory.Length` |
| `AlgebraicGeometry.Scheme.ord` | Mathlib, `Mathlib.AlgebraicGeometry.OrderOfVanishing` |
| `AlgebraicGeometry.GeometricallyConnected` | Mathlib, `Mathlib.AlgebraicGeometry.Geometrically.Connected` |
| `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` | Mathlib, `Mathlib.AlgebraicGeometry.Noetherian` |
| `AlgebraicGeometry.Scheme.Modules.pullback` | Mathlib, `Mathlib.AlgebraicGeometry.Modules.Sheaf` |
| `closedPoints` | Mathlib, `Mathlib.Topology.JacobsonSpace` |
| `AlgebraicGeometry.Scheme.Hom.functionFieldMap`, `AlgebraicGeometry.Scheme.Hom.ramificationIndex`, `AlgebraicGeometry.Scheme.Divisor.pullback`, `AlgebraicGeometry.Scheme.Divisor.degree_pullback_eq_finrank_functionField_mul`, `AlgebraicGeometry.Scheme.Hom.apply_genericPoint_of_flat`, `AlgebraicGeometry.Scheme.Hom.finrank_genericPoint_eq_finrank_functionField` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback` |
| `AlgebraicGeometry.Scheme.Divisor`, `AlgebraicGeometry.Scheme.Divisor.degree` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Curve.Divisor` |
| `AlgebraicGeometry.Scheme.Divisor.idealSheaf`, `AlgebraicGeometry.Scheme.Divisor.isInvertible_idealSheaf` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf` |
| `AlgebraicGeometry.Scheme.Divisor.degree_dual_toModules_idealSheaf` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Curve.DivisorDegree` |
| `AlgebraicGeometry.Scheme.IdealSheafData.toModules` | weil-conjectures, `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` |
| `AlgebraicGeometry.Scheme.Modules.dual` (notation `ᵛ`) | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Modules.Dual` |
| `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Modules.Differentials` |
| `AlgebraicGeometry.Scheme.Hom.genus` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Curve` |
| `AlgebraicGeometry.Scheme.Hom.degreeOver` | weil-conjectures, `WeilConjectures.ZetaSeries` |
| `AlgebraicGeometry.Scheme.globalSectionsRingHom` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Cohomology.Defs` |
| `AlgebraicGeometry.Scheme.arithmeticGenus`, `AlgebraicGeometry.Scheme.arithmeticGenus_pullback` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` |
| `AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`, `AlgebraicGeometry.Scheme.degree_relativeDifferentials`, `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_degree_add` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch` |
| `AlgebraicGeometry.Scheme.picDegreeHom_toPic` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Curve.Picard` |
| `AlgebraicGeometry.Scheme.isDiscreteValuationRing_stalk_of_isClosed` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.Curve.SerreDuality` |
| `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyConnected` | weil-conjectures, `WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective` |

The tensor product `⊗` on `Y.Modules` is the monoidal structure of
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`. The `#print axioms` results of the three
statements, which contain it, are the list above. The module defines no second version of the
curve, divisor, degree, genus, different or Kähler-differential notions: it uses the
declarations above.

## Sources

- Jean-Pierre Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979,
  `serre-1979-local-fields`, file
  `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`; printed page = PDF page − 7.
  The passages used are Chapter III: §3 (the different as the inverse of the codifferent, and
  Prop. 6, the discriminant is the norm of the different, p. 50), §4, Prop. 9 (localization,
  p. 51) and Prop. 10 (completion, p. 52), §6, Prop. 13 (with separable residue extension, the
  exponent is at least `e − 1`, with equality iff `e` is prime to the residue characteristic,
  p. 58), and §7, Prop. 14 (the annihilator of `Ω_A(B)` is the different, pp. 59–60). From
  Chapter IV, for Galois extensions, they are §1, Prop. 4 (`v_L(𝔇) = Σ_i (|G_i| − 1)`, p. 64)
  and §2, Prop. 7, Cor. 1 (`G_0/G_1` has order prime to the residue characteristic, p. 67).
  Serre's *Corrections to
  J-P. Serre's books* (2019), `serre-book-corrections-2019`, list no correction on these pages.
- Michel Raynaud, *Caractéristique d'Euler-Poincaré d'un faisceau et cohomologie des variétés
  abéliennes*, Séminaire Bourbaki 286 (1965), `raynaud-1965-bourbaki-286-euler-poincare`, file
  `/home/taskhub/pilot/literature/Raynaud - Caracteristique d'Euler-Poincare d'un faisceau et cohomologie des varietes abeliennes (Seminaire Bourbaki 286).pdf`,
  SHA-256 `fd0cf10b653f40e43f2ef7211fed427b7c5c80022c42bedecbf1544b050baa40`; printed page = PDF
  page + 127. The base field is algebraically closed and `χ(C) = 2 − 2g` (p. 129); `d(K'/K)` is
  the degree of the discriminant (p. 131, Prop. 1(c)). §4, Lemme 1 (pp. 133–134) treats the
  normalization `C'` of `C` in a finite separable extension `K'/K` and uses the Hurwitz formula,
  printed on p. 134 as `χ(C') = [K' : K] χ(C) + d(K' : K)`. With the conventions of pp. 129 and
  131 the sign of `d(K' : K)` must be a minus (see "The sign in Raynaud" above). The formulas
  were read on images of the pages, since text extraction drops them.
- Nicholas M. Katz, *Local-to-global extensions of representations of fundamental groups*,
  Ann. Inst. Fourier 36 (1986), `katz-1986-local-to-global-extensions`, file
  `/home/taskhub/pilot/literature/Katz - Local-to-global extensions of representations of fundamental groups (Ann. Inst. Fourier 36(4), 1986).pdf`,
  SHA-256 `de5a870ed52f6b0c66235cb4a5e6a3c4158b89ea8bd7f77f977b63d95694057b`; printed page = PDF
  page + 67. Coverings of `𝔾_m` tame at `0`, defined by pullback along invertible power maps,
  (1.1.2)–(1.1.3), pp. 71–72; monodromy and special coverings, (1.2)–(1.3), pp. 73–76; and
  Proposition (1.4.2), p. 79. These passages give the setting in which the design note applies
  the tame form of the formula. They do not state the formula, which comes from Riemann–Hurwitz
  and Serre III §6, Prop. 13.

## Scope

The module states the three propositions and proves none of them. Euler characteristics of
sheaves and the Grothendieck–Ogg–Shafarevich formula are outside it. Compilation and
`#print axioms` confirm that the module elaborates, that the three statements are propositions,
and that only the standard axioms are used. They do not establish the mathematics asserted.
