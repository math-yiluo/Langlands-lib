# Frames compatible with the actual adelic Weil pairing

This module specializes `PEL.FormIso` to the actual abelian-scheme Tate module
and actual Weil pairing. Its motivation is Harris–Taylor, *The Geometry and
Cohomology of Some Simple Shimura Varieties* (2001), Section III.1, pp.91–92,
and Kottwitz, *Points on some Shimura varieties over finite fields* (1992),
Section 5, pp.390–391. Harris–Taylor p.18 fixes the full and away rational Tate
modules as rationalizations of the integral inverse limits. These sources are
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura` and
`kottwitz-1992-points-shimura-finite-fields`.

Let `D` be a rational algebra, `V` a rational vector space with compatible
`D`-action, and `ψ` a rational bilinear form on `V`. Let `A/S` be an actual
abelian scheme with the existing dual-scheme geometry and Poincaré evaluation
inputs. The given algebra map `i : D →ₐ[ℚ] Rationalization.End A` supplies the
actual target action. The dual-valued homomorphism `polarizationMap` is an actual
abelian-scheme homomorphism. The pullback-tensor coherence, Picard pullback
and finite Weil transition statements remain explicit theorem dependencies.
The finite-adele scalar comparison is also explicit.

At a geometric point `s : Spec Ω → S`, `WeilAdelicFrame` consists of
`D ⊗[ℚ] A_f`-linear isomorphisms

`η : A_f ⊗[ℚ] V ≃ V A_s`

for which there exists an `A_f`-linear equivalence

`t : A_f ≃ A_f(1)_s`

satisfying `e_lam(η x, η y) = t ((ψ.baseChange A_f) x y)` for every `x,y`.
The source tensor order is Mathlib's ordinary scalar-extension convention.
Its `D ⊗[ℚ] A_f` action is `PEL.scalarExtensionAlgebraModule`, so a pure
tensor `d ⊗ a` acts on `r ⊗ x` as `(a*r) ⊗ (d • x)`.
The standard form is the scalar extension of the given rational form.
The target is the actual rationalized torsion inverse limit, with action
`finiteAdeleAlgebraModule`. Its form is
`adelicWeilAlongHomBilinearMap`, using the original finite Weil construction
and pullback by `polarizationMap` in the second variable.

The value module is precisely
`TateTwist.Divisibility.Rational Γ((Over.mk s).left, ⊤) (fun _ => True)`,
with its constructed finite-adele action. The definition makes no
identification of this section ring with `Ω`. A twist trivialization is
quantified existentially in the compatibility predicate; it is not retained
as part of a frame. By `PEL.formCompatible_iff`, after any fixed
trivialization this is exactly compatibility up to a unit scalar. There is
no choice of compatible roots of unity in the definition.

`WeilPrimeToAdelicFrame` uses the orders coprime to an arbitrary modulus
`m`, the ring `PrimeToFiniteAdeles m`, the actual away Tate module and twist,
and `awayAdelicWeilAlongHomBilinearMap`. Its full and away scalar comparisons
are coupled by `PrimeToRationalProfiniteIntegerAdeleComparison h m`.
Taking `m` to be a prime gives the prime-to-that-prime frame space.

The two `Underlying` maps forget the form condition and land in the
existing actual `AdelicFrame` and `PrimeToAdelicFrame` spaces.
The two `RightAction` definitions use the existing `FormIso` right action
by source similitudes, expressed as a left action of the opposite group.
The application lemmas give `(η · g)(x) = η(g(x))`. The action laws and
preservation of form compatibility are inherited from `FormIso`; its
construction adjusts the existential value trivialization by the unit
multiplier.

This is a derived specialization of the existing constructions. It imposes
no finite-dimensionality, faithfulness, involution compatibility,
alternation, nondegeneracy or polarization predicate. In the intended PEL
application those conditions belong to the rational datum and to the chosen
`polarizationMap`; the present definition also makes sense for any actual dual-valued
homomorphism. No nonemptiness assertion follows from this definition.
This module constructs the restricted frame spaces and their right
actions. Geometric monodromy preservation, fixed-orbit level structures and
their transport require compatibility theorems for the actual pairing.
