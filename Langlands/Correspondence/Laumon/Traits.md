# End traits of the Fourier lines and the character `ψ`

Laumon's local Fourier transforms live on henselian traits of equal characteristic
`p` with residue field `k` (Laumon 1987, (2.1.1), p. 151, and (2.4.1), p. 162). In
the proof of his Théorème (2.4.3) these traits are the henselizations of the projective
line `D` and of its dual `D'` at the rational ends `0`, `∞` and `0'`, `∞'`, with
uniformizers `x`, `1/x`, `x'`, `1/x'` (Lemme (2.4.2.1), p. 162). This module fixes one
model of these traits with all their points, and the additive character `ψ` of
Laumon (0.2), p. 134. Throughout, `k` is an arbitrary field; Laumon assumes `k` perfect
((0.1), p. 134), and the comparisons below say where this matters. Only the character needs
`k` finite.

## The model of the end traits

Laumon (2.1.1) observes that a henselian trait `R` with uniformizer `π` satisfies
`k{π} ⊂ R ⊂ k[[π]]`, where `k{π}` is the henselization of `k[π]_(π)`. The module
realizes all four end traits on a single ring of power series in one variable `t`.

- `endField k` is the separable closure of `k(t)` in `k((t))`: Mathlib's
  `separableClosure (RatFunc k) (LaurentSeries k)`. Rational functions are expanded
  at `t = 0` through `laurentSeriesRatFuncAlgebra`, which is Mathlib's scoped
  instance `RatFunc.liftAlgebra` specialized to `LaurentSeries k`.
- `endRing k` is the subring of `endField k` of the elements that are power series,
  i.e. lie in the image of `HahnSeries.ofPowerSeries ℤ k`.
- `endConstantHom k : k →+* endRing k` gives the constants. Its values are the
  constant power series (`algebraMap_ratFunc_algebraMap`).
- `endUniformizer k e` is the series `t` itself, for every end `e`
  (`algebraMap_ratFunc_X`). The ends differ by the global coordinate that is pulled
  back to `t`, described below.
- `endPowerSeriesHom k` recovers the power series of an element of `endRing k`, and
  `endResidue k` is its constant coefficient, the residue map to `k`.

`EndTraitHenselizationStatement` states that this model is the henselization: for every
field `k`, `endRing k` is a henselian local ring and a discrete valuation ring, `t` is
irreducible in it, and every ring map `φ : k[x] → B` to a henselian local ring `B` with
`φ⁻¹(𝔪_B) = (x)` extends along `x ↦ t` to a unique local ring map `endRing k → B`. Ring
maps from `k[x]` with this property are the local maps from `k[x]_(x)`, so the last clause
is the universal property of the henselization of `k[x]_(x)` (Stacks Project, Section
10.155: Lemma 10.155.1 for its construction, Lemma 10.155.6 for its functoriality, and the
uniqueness statement after Definition 10.155.3). The statement is true for every field `k`.
The henselization `k{x}` lies in `k[[x]]`, and its fraction field is a union of finite
separable extensions of `k(x)` (Lemma 10.155.1: `k{x}` is a filtered colimit of étale
`k[x]_(x)`-algebras). Hence `k{x} ⊂ endRing k`. Conversely, let `R` be a henselian
discrete valuation ring with an injective map `R → k[[t]]` that sends a uniformizer to a
series of order one and has surjective residue map. Then every element of `k((t))`
separable over the fraction field of `R` lies in that fraction field. This is
`IsDiscreteValuationRing.mem_range_fractionRingMap_of_isSeparable` of weil-conjectures
(module `WeilConjectures.TraceFormula.Specialization.HenselianTraitLaurentSepClosed`),
which depends only on `propext`, `Classical.choice` and `Quot.sound`; this module does not
import it. Applied to `R = k{x}`, it shows that an element of `endRing k` lies in the
fraction field of `k{x}`; as it has nonnegative valuation, it lies in `k{x}`. This module
states the property and does not prove it.

## The four ends and their maps to the global lines

`FourierEnd` has the constructors `zero`, `infinity`, `dualZero` and `dualInfinity` for
`0`, `∞`, `0'` and `∞'`. `FourierEnd.coordinateExponent` is `1` at `0` and `0'`, and `-1`
at `∞` and `∞'`.

- `endTrait k e` is `Spec (endRing k)` and `puncturedEnd k e` is `Spec (endField k)`,
  the generic point `η` of the trait. `puncturedEndToTrait k e` is the inclusion.
- `endChartCoordinate k e : k[X] →+* endRing k` sends the variable to `t`, and
  `endTraitToChart k e` is the induced map to weil-conjectures's
  `AlgebraicGeometry.affineLine k`, via `AlgebraicGeometry.affineLine.isoSpecPolynomial`.
  At `0` and `0'` the target is the affine chart of `D` or `D'` with coordinate `x` or `x'`.
  At `∞` and `∞'` it is the affine chart at infinity, with coordinate `1/x` or `1/x'`.
- `infinityChart S` is the open immersion `𝔸¹_S → ℙ¹_S`, `y ↦ [1 : y]`, onto the standard
  open `D₊(T₀)`, built like weil-conjectures's `AlgebraicGeometry.ProjectiveLine.affineChart`
  (`x ↦ [x : 1]`, onto `D₊(T₁)`) from `AlgebraicGeometry.ProjectiveSpace.standardOpenIso`.
  The two coordinates `T₀/T₁` and `T₁/T₀` are inverse on the overlap.
- `endTraitToProjectiveLine k e` is the map of the end trait to the projective line
  `AlgebraicGeometry.ProjectiveLine (Spec k)` (the line `D` or `D'`): `endTraitToChart k e`
  followed by `affineChart` at `0` and `0'`, and by `infinityChart` at `∞` and `∞'`. It
  pulls back `x = T₀/T₁` (or `x'`) to `t` at `0` (or `0'`) and `1/x = T₁/T₀` (or `1/x'`) to
  `t` at `∞` (or `∞'`). These are the `k`-morphisms `π : T → A` and `π : T → D` of Laumon's
  Lemme (2.4.2.1)(i)–(iii), p. 162, defined by `π ↦ x` and `π ↦ 1/x`, and the corresponding
  maps for the dual line.
- `endLineCoordinate k e = t ^ coordinateExponent e` is the global coordinate on the
  punctured end, and `puncturedEndToLine k e : η → A` (or `A'`) is the induced map. The
  punctured end maps into the affine chart `A` of `D` at every end: at `∞` its image lies
  in the overlap of the two charts, where `x = 1/(1/x)`, so `puncturedEndToLine k e` is the
  restriction of `puncturedEndToTrait k e ≫ endTraitToProjectiveLine k e` to `A`. It is not
  the primed arrow `π' : η' → η_{0'}` or `η_{∞'}` of Lemme (2.4.2.1), which goes from the
  target trait to the generic point of the henselization of the dual line at `0'` or `∞'`.
  In this model that henselization is again `puncturedEnd k dualZero` or
  `puncturedEnd k dualInfinity`, with `π' ↦ x'` or `π' ↦ 1/x'` meaning `t ↦ t`, so the primed
  arrow is the identity of the model.

## Generic, strict and geometric points

Laumon (2.1.1), p. 151, and (0.4), p. 134, use a geometric generic point `η̄` that
factors through the generic point `η₁` of the strictly henselian trait over `T`, and the
geometric special point `t̄ : Spec k̄ → Spec k → T`.

- `endGenericClosure k` is the separable closure of `endField k` inside
  `SeparableClosure (LaurentSeries k)`. With this choice the separable closure of the
  henselian fraction field lies inside the separable closure of its completion `k((t))`,
  which is the closure used by the Library's local Galois groups of `LaurentSeries k`.
- `endGeometricGenericPoint k e` is `Spec Ω̄ → Spec Ω → η` with
  `Ω = endGenericClosure k` and `Ω̄ = AlgebraicClosure Ω`. It is weil-conjectures's
  `AlgebraicGeometry.Scheme.FiniteEtale.pointOfAlgebra Ω̄ (𝟙 η)`, so that the fibre
  functor, its Galois action `galoisToAut` and the monodromy of lisse sheaves of
  weil-conjectures, which use geometric points valued in an algebraic closure, apply
  to it directly.
- `endConstants k` is the algebraic closure of `k` in `Ω`, and `endConstantsHom k` the
  inclusion of `k`. As `Ω` is separable over `k(t)` and an irreducible polynomial over `k`
  stays irreducible over `k(t)`, its elements are separable over `k`; and every separable
  polynomial over `k` splits in `Ω`. So `endConstants k` is a separable closure `k^sep` of
  `k`, and the algebraic closure when `k` is perfect, e.g. finite. `endUnramifiedField k` is the subfield of `Ω` generated over
  `endField k` by `endConstants k`. The finite unramified extensions of a discretely
  valued field `K` with residue field `k` correspond to the finite separable extensions
  `k'/k`, the one attached to `k'` being `k' ⊗_k K` in equal characteristic; their union
  is the maximal unramified extension (Serre, *Local Fields*, III §5, Theorems 2–3 and
  Corollary 1, pp. 54–55, and Remark 1, p. 55, for complete `K`; the proof uses
  completeness only through Hensel's lemma). For the henselian ring `endRing k` the
  corresponding construction of the strict henselization is Remark 10.155.4 of the
  Stacks Project. So `endUnramifiedField k` is the maximal unramified subextension of `Ω`:
  the fraction field of `endRing k ⊗_k k^sep`, generated over `endField k` by `k^sep`. Laumon
  (2.1.1) assumes `k` perfect ((0.1), p. 134) and writes `Spec(k̄ ⊗_k R)` for the strict
  trait; for perfect `k`, in particular for the finite fields of the application,
  `k^sep = k̄` and the two descriptions agree. For imperfect `k` they differ: a root of
  `X^p − s` for `s ∈ k ∖ k^p` lies in `k̄ ⊗_k R` but not in `Ω`.
- `endStrictRing k` is the integral closure of `endRing k` in `endUnramifiedField k`, and
  `endStrictTrait k` its spectrum, the chosen strict target trait. `endStrictTraitToTrait`
  is its map to the end trait at `e` and `endStrictGenericPoint k e` the map of its generic
  point `η₁` to `η`. The geometric generic point lies over `η₁`, as
  `endUnramifiedField k ⊂ Ω`.
- `endGeometricSpecialPoint k e` is `Spec k̄ → Spec k → T`, through `endResidue k`, with
  `k̄ = AlgebraicClosure k`, as in Laumon (0.4) for a rational point. The residue field of the
  strict target trait is `endConstants k`, a separable closure of `k`. For finite `k` it is
  an algebraic closure of `k`, so a `k`-isomorphism `endConstants k ≅ AlgebraicClosure k`
  exists, and composing with it the geometric special point lifts to the strict target
  trait. The isomorphism is not unique, and this module does not choose one.

## The Fourier character

Laumon (0.2), p. 134, fixes a nontrivial additive character `ψ : 𝔽_p → ℚ̄_ℓ`, i.e. a
primitive `p`-th root of unity `ψ(1)`, and puts `ψ_q(a) = ψ(Tr_{𝔽_q/𝔽_p}(a))`. Here
`ℓ` is a prime, `E = PadicAlgCl ℓ`, and `k` is finite with `p = ringChar k`.

- `fact_ringChar_prime` records that `p` is prime.
- `fourierRoot k ℓ` is a chosen primitive `p`-th root of unity of `E`. It exists since
  `E` is algebraically closed of characteristic zero (Mathlib's
  `HasEnoughRootsOfUnity.exists_isPrimitiveRoot`), as `fourierRoot_isPrimitiveRoot`
  records.
- `fourierCharacter k ℓ : AddChar k E` is `a ↦ ζ ^ Tr_{k/𝔽_p}(a)`: Mathlib's
  `AddChar.zmodChar p` for `ζ = fourierRoot k ℓ`, composed with
  `Algebra.trace (ZMod p) k`. This is the same type of character as the argument of
  weil-conjectures's Fourier transforms (`AlgebraicGeometry.WeilSheaf.fourierTransform`
  takes an `AddChar k₀ (PadicAlgCl l)`).
- `fourierCharacter_ne_one` proves that `ψ` is nontrivial: the trace form of `k` over
  `𝔽_p` is nondegenerate (`FiniteField.trace_to_zmod_nondegenerate`), so some `a` has
  `Tr(a) ≠ 0`, and the character of `ZMod p` defined by a primitive root takes the value
  `1` only at `0`.

## External declarations

The module imports `Langlands.MathlibBase` and three modules of weil-conjectures. It uses
the following declarations of weil-conjectures, each of which depends only on
`propext`, `Classical.choice` and `Quot.sound` under `#print axioms`:

| Declaration | Module |
|---|---|
| `AlgebraicGeometry.affineLine` | `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace` |
| `AlgebraicGeometry.affineLine.isoSpecPolynomial` | `WeilConjectures.AlgebraicGeometry.AffineSpace.PolynomialMap` |
| `AlgebraicGeometry.Scheme.FiniteEtale.pointOfAlgebra` | `WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction` |
| `AlgebraicGeometry.ProjectiveLine` | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` |
| `AlgebraicGeometry.ProjectiveSpace.standardOpen` | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections` |
| `AlgebraicGeometry.ProjectiveLine.affineChart`, `AlgebraicGeometry.ProjectiveSpace.standardOpenIso` | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts` |

It also uses Mathlib's `AlgebraicGeometry.AffineSpace.reindex`. Every declaration of this
module also depends only on these three axioms.
