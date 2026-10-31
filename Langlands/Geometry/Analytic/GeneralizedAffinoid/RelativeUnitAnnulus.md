# The actual relative unit annulus and its canonical maps

Author: Worker 59. This focused construction specializes the published
`RelativeRelations`, `RelativeEvaluation` and `BinaryLaurentDiagram` APIs.
All declarations lie in
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus`.

## Parameters and actual quotient

Fix `K : Type u` with `[NormedField K] [IsUltrametricDist K]` and an arbitrary
`A : PresentedAffinoidAlgebra K`. Write

```text
rₙ = PositivePolyradius.unit (Fin n)
Tₙ = GeneralizedTateAlgebra rₙ A
Cₙ = GeneralizedTateAlgebra.constantAlgHom rₙ K A
Xᵢ = GeneralizedTateAlgebra.X r₂ A i
```

The declarations are universe polymorphic. The base may be zero or nonreduced.
No nontriviality of the valuation, properness of an ideal, spectrum point, or
bound on a chosen `f : A` is assumed. Completeness of `K` is used only in the
section constructing the evaluation maps and their laws. The quotient,
coefficient maps, coordinates, norm bounds, unit relation, `hom_ext` and
the helper `overlapCoordinate` and its bounds do not require it.

`equations K A` is exactly the singleton `{X₀ * X₁ - 1}` in `T₂`.
`Algebra K A` is the abbreviation

```lean
RelativeRelations.QuotientAlgebra K A
  (PositivePolyradius.unit (Fin 2)) (equations K A)
```

Thus its carrier is the actual ring quotient

\[
\mathcal U_A =
 A\langle X_0,X_1\rangle/
 \overline{\operatorname{span}\{X_0X_1-1\}}.
\]

Here `span` is ideal generation. The `NormedCommRing`, `NormedAlgebra K`,
`Algebra A`, `IsScalarTower K A` and `IsUltrametricDist` instances are
inherited unchanged from `RelativeRelations.QuotientAlgebra`. Under
`[CompleteSpace K]`, its published completeness instance applies. No new
`PresentedAffinoidAlgebra` presentation is chosen. Its norm is the inherited
quotient norm. In particular, `exists_representative_norm_lt` states that for
`a : Algebra K A` and `ε > 0` there exists `h : T₂` such that
`quotientMap K A h = a` and `‖h‖ < ‖a‖ + ε`.

## Quotient projection, coefficients and coordinates

`quotientMap K A : BoundedAlgHom K T₂ (Algebra K A)` is the published
closed-quotient projection. Its representative formula is

```lean
quotientMap K A h =
  Ideal.Quotient.mk ((Ideal.span (equations K A)).closure) h
```

(`quotientMap_apply`). It is surjective (`quotientMap_surjective`).
`quotientMap_eq_zero_iff` gives

```lean
quotientMap K A h = 0 ↔ h ∈ (Ideal.span (equations K A)).closure
```

and `ker_quotientMap` identifies
`RingHom.ker (quotientMap K A).toAlgHom` with that same closed ideal.
`norm_quotientMap_le` states `‖quotientMap K A h‖ ≤ ‖h‖`. These laws and
the norm-approximation law above directly specialize `RelativeRelations`.

`baseMap K A : BoundedAlgHom K A (Algebra K A)` is the canonical coefficient
map. `coordinate K A i`, for `i : Fin 2`, is the quotient image of `Xᵢ`.
The names `annulusX K A` and `annulusY K A` abbreviate coordinates `0` and
`1`. Their exact representative formulas are

\[
c(a)=q(C_2(a)),\qquad x=q(X_0),\qquad y=q(X_1),
\]

where `c = baseMap K A`, `q = quotientMap K A`, `x = annulusX K A` and
`y = annulusY K A`. The declarations are `baseMap_apply`, `coordinate_def`,
`annulusX_def` and `annulusY_def`. `baseMap_eq_algebraMap` also states that
`baseMap K A a = algebraMap A (Algebra K A) a`.

The inherited bounds are

\[
\|c(a)\|\leq\|a\|,\qquad \|\operatorname{coordinate}(i)\|\leq1,
\qquad \|x\|\leq1,\qquad\|y\|\leq1.
\]

They are `norm_baseMap_le`, `norm_coordinate_le`, `norm_annulusX_le` and
`norm_annulusY_le`. `norm_one_le` gives `‖(1 : Algebra K A)‖ ≤ 1`, using
the coefficient bound and `PresentedAffinoidAlgebra.norm_one_le`; it covers
the empty monomial even in the zero quotient.

`annulusX_mul_annulusY` proves `x * y = 1`. Its proof projects the actual
singleton equation using `RelativeRelations.quotientMap_equation` and
rewrites preservation of subtraction, multiplication and one. This does not
require a Laurent expansion.

For any independently universe-polymorphic normed commutative `K`-algebra
`B`, `hom_ext` says that two `BoundedAlgHom K (Algebra K A) B` agreeing on
all `baseMap` images and on `annulusX` and `annulusY` are equal. It combines
`GeneralizedTateAlgebra.relative_hom_ext` on the relative series algebra with
`RelativeRelations.hom_ext` on the quotient. Neither completeness nor
ultrametricity of `B` is needed.

## Positive and negative maps

Assume `[CompleteSpace K]` for the rest of the map constructions. This makes
`A`, its relative series, the annulus and the existing overlap complete via
their published instances.

`oneVariable K A i`, for `i : Fin 2`, is a bounded `K`-algebra map
`T₁ → Algebra K A` built by `evaluateCoefficientsHom`. It uses coefficient
map `baseMap K A` and the constant coordinate tuple
`fun _ : Fin 1 => coordinate K A i`. Its bounds come from
`monomialValue_norm_le_weight`, `norm_one_le`, `norm_coordinate_le` and
`norm_baseMap_le`. The two requested maps are

```lean
positive K A = oneVariable K A 0
negative K A = oneVariable K A 1
```

For `h : T₁`, `oneVariable_apply`, `positive_apply` and `negative_apply`
give their actual coefficient-evaluation formulas:

```lean
positive K A h =
  evaluateCoefficients r₁ (baseMap K A) (fun _ => annulusX K A) h
negative K A h =
  evaluateCoefficients r₁ (baseMap K A) (fun _ => annulusY K A) h
```

The shorthand `r₁` is as defined above; the Lean file writes it in full.
Concretely, for coefficients `a_d` of `h` indexed by `d : Fin 1 →₀ ℕ`,
these are the convergent sums

\[
p(h)=\sum_d c(a_d)x^{d(0)},\qquad
n(h)=\sum_d c(a_d)y^{d(0)}.
\]

The imported evaluation is the sum of the coefficient image times
`StrictTateAlgebra.monomialValue`; in one variable that product is the
displayed power. No coefficient extraction or Laurent normal form on the
quotient is constructed here.

`oneVariable_constant` and `oneVariable_X` give the coefficient and variable
values for either index. Their named specializations are

\[
p(C_1(a))=c(a),\quad n(C_1(a))=c(a),\quad
p(X_{r_1,j})=x,\quad n(X_{r_1,j})=y
\quad(j:\operatorname{Fin}1).
\]

These are `positive_constant`, `negative_constant`, `positive_X` and
`negative_X`. `norm_oneVariable_le`, `norm_positive_le` and
`norm_negative_le` state contractivity on every input `h : T₁`. The proofs
specialize `norm_evaluateCoefficients_le`. The names “positive” and “negative”
refer to the two coordinate evaluations.

## Canonical map to the actual binary overlap

Fix any `f : A`. All overlap objects and maps here are the published
`BinaryLaurent` ones. Put `O = BinaryLaurent.Overlap K A f`,
`b = BinaryLaurent.overlapBase K A f`,
`x_O = BinaryLaurent.overlapX K A f` and
`y_O = BinaryLaurent.overlapY K A f`. `overlapCoordinate K A f i` is `x_O`
at `i = 0` and `y_O` at `i = 1`. The lemmas `overlapCoordinate_zero`,
`overlapCoordinate_one` and `norm_overlapCoordinate_le` give these formulas
and their unit bounds.

`toOverlapSeries K A f : BoundedAlgHom K T₂ O` is the actual relative
coefficient evaluation through `b` at this two-coordinate tuple.
`toOverlapSeries_constant` and `toOverlapSeries_X` give the defining values
`C₂(a) ↦ b(a)` and `Xᵢ ↦ overlapCoordinate K A f i`.
`norm_toOverlapSeries_le` proves its contractivity using the published
overlap coefficient, coordinate and unit bounds.

`toOverlapSeries_equations` proves annihilation of the annulus equation by
the following calculation, using precisely the existing overlap relations:

\[
x_Oy_O-1=b(f)y_O-1=1-1=0.
\]

The first equality is `BinaryLaurent.overlapX_eq`; the second is
`BinaryLaurent.overlapBase_mul_overlapY`. The singleton equation is therefore
annihilated. `toOverlap K A f : BoundedAlgHom K (Algebra K A) O` is its
`RelativeRelations.descend` through the closed ideal. Continuity and the
published descent API supply vanishing on the closure; no closedness of an
ordinary generated ideal is asserted.

For every representative `h : T₂`, `toOverlap_quotientMap` states

```lean
toOverlap K A f (quotientMap K A h) =
  evaluateCoefficients r₂ (BinaryLaurent.overlapBase K A f)
    (overlapCoordinate K A f) h
```

Thus on coefficients and coordinates,

\[
F(c(a))=b(a),\qquad F(x)=x_O,\qquad F(y)=y_O,
\]

where `F = toOverlap K A f`. These are `toOverlap_baseMap`,
`toOverlap_annulusX` and `toOverlap_annulusY`; `toOverlap_coordinate` gives
the indexed version. `norm_toOverlap_le` states `‖F(a)‖ ≤ ‖a‖` for every
annulus element. It applies `RelativeRelations.norm_descend_le` with bound
one to `norm_toOverlapSeries_le`, so it uses the actual quotient norm.
`toOverlap_comp_baseMap` is the bounded-map equality `F.comp c = b`.
`eq_toOverlap` specializes `hom_ext` to show uniqueness among bounded maps
with these coefficient and coordinate values.

## Compatibility on the original one-variable representatives

Let `q₊` and `q₋` denote the actual published quotient maps

```lean
q₊ = RelativeRationalPresentation.quotientMap K A r₁ 1 (fun _ => f)
q₋ = RelativeRationalPresentation.quotientMap K A r₁ f (fun _ => 1)
```

Their targets are `BinaryLaurent.Upper K A f` and
`BinaryLaurent.Lower K A f`, respectively. With all polyradii written out
in Lean, `toOverlap_comp_positive` and `toOverlap_comp_negative` prove
equalities of bounded maps

\[
F\circ p=\mathrm{BinaryLaurent.left}\circ q_+,\qquad
F\circ n=\mathrm{BinaryLaurent.right}\circ q_-.
\]

They use `relative_hom_ext` on `T₁`. On constants the defining maps agree by
`toOverlap_baseMap` and `BinaryLaurent.left_upperBase` or
`BinaryLaurent.right_lowerBase`. On the sole variable they agree by the
coordinate formulas and `BinaryLaurent.left_upperX` or
`BinaryLaurent.right_lowerY`. Consequently, for every `h : T₁`,
`toOverlap_positive` and `toOverlap_negative` give the pointwise identities

```lean
toOverlap K A f (positive K A h) =
  BinaryLaurent.left K A f
    (RelativeRationalPresentation.quotientMap K A r₁ 1 (fun _ => f) h)
toOverlap K A f (negative K A h) =
  BinaryLaurent.right K A f
    (RelativeRationalPresentation.quotientMap K A r₁ f (fun _ => 1) h)
```

These compare the actual canonical maps and quotients directly.

## Original source, derived construction and boundaries

The retained original is Piotr Achinger, *Introduction to non-Archimedean
Geometry*, November 22, 2020, registered as
`achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`,
at `/home/taskhub/pilot/literature/Piotr Achinger, Introduction to non-Archimedean Geometry (November 22, 2020).pdf`.
Printed/PDF page 6 and pages 63–65 were read directly for this unit.
The literature-index entry was checked; a bounded filename search of retained
literature and current Library notes found no Achinger-specific errata.

In the proof of Proposition 7.1.1, p.64, Achinger defines
`A⟨X,X⁻¹⟩ = A⟨X,Y⟩/(XY-1)` and uses the positive and negative
one-variable maps in the preliminary Laurent sequence. This module constructs
that auxiliary quotient and its maps in the published relative-series
framework, replacing the ordinary generated ideal by its closure and
retaining the actual quotient norm. It neither identifies the plain ideal
with its closure nor asserts the Laurent normal form used in the source's
exactness argument. Page 6 assumes a complete, nontrivially valued scalar
field. Completeness is retained for constructing the convergent evaluations;
nontrivial valuation is unnecessary for these elementary constructions and
is not imposed. The quotient and elementary algebraic laws also work without
completeness. The source's later small-scalar reductions are not used.

Page 63 places the binary Laurent sequence in Tate acyclicity, and page 65
passes to general Laurent coverings. The displayed proposition on p.64
omits the words “is exact”; its last paragraph has `g₋₁` where `g₋` is
intended. These discrepancies are also recorded in the published
`BinaryLaurentGluingStatement.md`. Neither exactness argument is implemented
by this definition unit.

The overlap map, the contraction estimates and the compatibility identities
are derived here from the published bounded relative evaluation, quotient
descent and map uniqueness APIs. They are not cited as separate statements
of Achinger. Existing `RelativeRelations`, `RelativeEvaluation`,
`BinaryLaurentDiagram` and all their imported Lean/Markdown pairs remain
unchanged. Importing their declarations does not add their authors as
coauthors of this new specialization.

This unit constructs no coefficient normal form, injectivity theorem,
ordinary-ideal closedness theorem, comparison kernel, algebra equivalence,
exact sequence or gluing theorem. The relative scalar gluing target
`BinaryLaurent.GluingStatement`, strict binary assembly and the strict/relative
diagram comparison remain separate. There is no circular use of gluing.
