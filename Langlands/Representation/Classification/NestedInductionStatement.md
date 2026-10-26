# Normalized induction in stages inside a product Levi

Authors: Worker 519 and Worker 156.

`Langlands.NormalizedNestedInductionStatement.{uF,uV,uM,uW}` is the conjunction
of `Langlands.NestedInduction.Comparison.{uF,uV}` and
`Langlands.NestedInduction.QuotientTransport.{uF,uV,uM,uW}`. All three
declarations are `Prop`-valued definitions. This module states the comparison
and the quotient consequence; it supplies no proof of either.

## Fields, ordered refinements, and actual representations

Each clause quantifies every prime `p` with `[Fact p.Prime]`, an actual
`F : PadicField.{uF} p`, compatible `T : F.TopologicalData`, an arbitrary
natural rank `n`, `B : GeneralLinear.BlockShape n`, and
`Q : Geometric.BlockRefinement B`. Set

```text
D := B.flatten Q
R : Geometric.BlockRefinement D
S := B.composeRefinement Q R
h := B.flatten_composeRefinement Q R : D.flatten R = B.flatten S.
```

Here `R` is arbitrary, whereas `D`, `S`, and `h` are the displayed Library
constructions. In particular, `S` and `h` are not supplied comparison data.
The imported `Langlands.Group.GL.NestedRefinement` constructs `S` by ordered
concatenation within every `B` block and proves the literal shape equality
`h`. Consequently, transport along `h` respects the consecutive fine-block
order, including each fine-block rank.

The statements use the existing actual representations
`RelativeRegularComparison.middleInduced`,
`RelativeJacquetMultiplicity.innerInduced`, and
`RelativeJacquetMultiplicity.fineTwist`. For any shape `X`, refinement `Y`,
and representation `η` of `(X.flatten Y).Levi F.Carrier`,
`middleInduced T X Y η` first pulls `η` back along
`(Geometric.flattenedLeviEquiv F.Carrier X Y).symm` and then uses
`innerInduced T X Y`. The latter is `T.normalizedRefinedInduced X Y` on the
actual smooth covariant-function carrier in `X.Levi F.Carrier`.
No replacement induction or arbitrary group equivalence is introduced.

## Comparison and both evaluation formulas

The first clause quantifies an arbitrary `V : Type uV` with
`[AddCommGroup V] [Module ℂ V]` and an arbitrary

```text
ω : Representation ℂ ((D.flatten R).Levi F.Carrier) V.
```

Transport changes the acting fine Levi while keeping the same coefficient
space and its module structures:

```text
ωB : Representation ℂ ((B.flatten S).Levi F.Carrier) V := h ▸ ω
A := middleInduced T B Q (middleInduced T D R (Rep.of ω))
C := middleInduced T B S (Rep.of ωB).
```

The assertion is the existence of an actual equivariant linear equivalence
`E : A.ρ.Equiv C.ρ` satisfying both formulas below. Evaluation is always the
existing `Induction.eval`, and `1` is the identity of `D.Levi F.Carrier`.
For every `f : A` and `g : B.Levi F.Carrier`,

```text
Induction.eval _ _ (E f) g
  = Induction.eval _ _ (Induction.eval _ _ f g) 1.
```

For every `f : C`, `g : B.Levi F.Carrier`, and `m : D.Levi F.Carrier`,
write `e := Geometric.flattenedLeviEquiv F.Carrier B Q`. Then

```text
Induction.eval _ _ (Induction.eval _ _ (E.symm f) g) m
  = (T.refinedLeviHalfModulus B Q (e m) : ℂ)⁻¹ •
      Induction.eval _ _ f ((e m).val * g).
```

Thus the forward map evaluates the middle function at its identity. The
inverse uses the inverse of the first refined positive half-modulus,
evaluated at the actual embedded middle element `e m`, and left-multiplies
the argument by `(e m).val` inside `B.Levi F.Carrier`. The nested function
takes values in an induced carrier, so the comparison is not an equality
of the same underlying functions.

The normalization is the Library's positive-half covariance and right
translation convention: for the actual refined parabolic and its Levi
projection `ℓ`, the induced function satisfies
`f(q g) = δ(ℓ(q))^(1/2) • η(ℓ(q))(f(g))`, and the group action is
`(x · f)(g) = f(g x)`. The displayed inverse scalar is essential with this
convention.

## Surjective-quotient transport

The second clause uses the same field, shapes, refinements, and constructed
`S` and `h`. It quantifies arbitrary

```text
ω : Rep.{uV} ℂ ((D.flatten R).Levi F.Carrier)
v₀ : Fin (D.flatten R).length → ℝ
σ : Rep.{uM} ℂ (D.Levi F.Carrier)
π : Rep.{uW} ℂ (B.Levi F.Carrier)
qFineMiddle :
  (innerInduced T D R (fineTwist T D R ω v₀ 0)).ρ.IntertwiningMap σ.ρ
qMiddleCoarse :
  (middleInduced T B Q σ).ρ.IntertwiningMap π.ρ.
```

Its only additional hypotheses are `Function.Surjective qFineMiddle` and
`Function.Surjective qMiddleCoarse`. It asserts an actual intertwiner

```text
qFineCoarse :
  (innerInduced T B S
    (fineTwist T B S (h ▸ ω) (h ▸ v₀) 0)).ρ.IntertwiningMap π.ρ
```

with `Function.Surjective qFineCoarse`. Both the bundled representation
`ω` and its real fine-coordinate family `v₀` are transported by exactly
the constructed equality `h`, in its displayed direction.

The existing `fineTwist T X Y ω v₀ t` uses determinant exponents
`k ↦ -v₀ k + t ((X.flattenBlockEquiv Y).symm k).1` before pullback to the
actual refined Levi. Here `0` is the zero outer exponent family, so the
fine exponent is precisely `-v₀`. There is no regularity, positivity, or
unitarity condition on `v₀`. This clause is the algebraic third-surjection
construction needed by `Langlands.GLTemperedJointSupportStatement`; it
does not choose support data or assert any analytic support theorem.

## Universes and scope

The field universe `uF` and all three coefficient universes `uV`, `uM`, and
`uW` are independent. Actual induction of a `uV`-valued representation has
carrier universe `max uF uV`. Iterating it gives
`max uF (max uF uV) = max uF uV`; the comparison does not force a carrier
into a smaller universe or identify it with the original `V`. The
middle-to-coarse induction of `σ` similarly has universe `max uF uM`.
There is no equality premise between any coefficient universes.

Every ordered shape is allowed, including rank zero and empty indexing
families. There is no positive-rank, smoothness, irreducibility,
admissibility, unitarity, temperedness, finite-length, finite-dimensionality,
or tensor-presentation premise on the representations. In particular, the
first comparison concerns constructed smooth parts even when `ω` is not
smooth. For the quotient clause, the fine induced source is smooth by its
construction, and surjectivity of `qFineMiddle` transfers smoothness to
`σ`; establishing and using these facts belongs to the later proof.
Neither transitivity, exactness, a modulus identity, another comparison,
nor a section of a surjection is assumed as theorem-valued input.

## Original source and internal derivation

The retained original is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS
(4) 10 (1977), 441–472, registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained PDF is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
Printed pp.443–446 (PDF pages 4–7) were read directly, with the induction
definition on p.444 and the propositions on pp.445–446 checked visually.
Section 1.2 identifies the paper's algebraic representations with smooth
representations. Section 1.8(a) specifies positive-half covariance, right
translation, and a single open right stabilizer for each induced function.
Proposition 1.9(a,c), p.445, states exactness and induction in stages, and
the following paragraph explicitly requires compatibility of the
normalizing factors. Section 2.2, p.446, identifies standard GL Levis
with ordered partitions and nested refinements. Proposition 2.3(a,c)
gives the corresponding exactness and transitivity for standard Levis.
No applicable source errata file was found in the current Library or
project notes in this task's bounded native search.

The source theorem concerns smooth inducing representations. The present
arbitrary-input smooth-part formulation, exact ordered finite-coordinate
transports, rank-zero case, explicit evaluation formulas, and quotient API
are internal derived targets. The comparison is to be established by the
uniform-open-stabilizer construction for the actual product-Levi tower.
The existing proof
`Langlands.Parabolic.normalizedRefinementInductionTransitivity` illustrates
evaluation at the inner identity and the inverse scalar formula for a
different ambient GL endpoint. Its public theorem is categorical on
smooth inputs; its private function construction permits arbitrary
inducing representations. The present extension does not follow from
that public categorical statement alone.

The quotient consequence is to follow by applying actual normalized
product-Levi induction to `qFineMiddle`, proving its induced map is
surjective, comparing the nested and direct induction, checking the
`h`-transport compatibility of `fineTwist`, and composing with
`qMiddleCoarse`. Those proof obligations, including the needed
product-Levi exactness specialization, remain open here. No shared
normalization, composed-to-flat, tensor, general exactness, analytic
support, or regular-head theorem is proved in this module.

Worker 156 supplied the elaborated interface scaffold reused for the two
clauses. Worker 519 checked the retained source and existing interfaces,
adapted the scaffold to the public names, and wrote this companion
explanation. Existing Library pairs are unchanged.
