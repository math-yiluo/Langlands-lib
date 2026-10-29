# The actual relative-series binary Laurent diagram

Authors: Worker 948 and Worker 101. This is a definition unit with elementary
map laws. It is built from published relative series, coefficient evaluation
and closed-ideal quotient descent.

## Concrete quotients and conventions

All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent`, with explicit
parameters `(K) (A : PresentedAffinoidAlgebra K) (f : A)`. Here `K` is a normed
field with an ultrametric norm. Only the arrows `left` and `right` and their
laws additionally assume `[CompleteSpace K]`, which makes the target quotient
complete.

Write `rₙ = PositivePolyradius.unit (Fin n)`, `C` for the bounded constant-series
inclusion `GeneralizedTateAlgebra.constantAlgHom rₙ K A`, and `Xᵢ` for the
published relative variable `GeneralizedTateAlgebra.X rₙ A i`. The objects are
actual quotients with the inherited quotient norms:

\[
\begin{aligned}
\mathrm{Upper}&=A\langle X\rangle/
 \overline{\langle X-C(f)\rangle},\\
\mathrm{Lower}&=A\langle Y\rangle/
 \overline{\langle C(f)Y-1\rangle},\\
\mathrm{Overlap}&=A\langle X,Y\rangle/
 \overline{\langle X-C(f),C(f)Y-1\rangle}.
\end{aligned}
\]

`Upper` is `RelativeRationalPresentation.Algebra K A r₁ 1 (fun _ => f)`: one
unit-radius variable, denominator `1` and numerator `f`. `Lower` is
`RelativeRationalPresentation.Algebra K A r₁ f (fun _ => 1)`: denominator `f`
and numerator `1`. These are the same denominator and numerator choices as the
strict `StrictTestDomain.RationalData.laurentUpper` and `laurentLower` data;
no comparison with them is proved here. `upperEquations_eq` and
`lowerEquations_eq` prove that the rational equation ranges are exactly the
singletons `{X₀ - C(f)}` and `{C(f) * X₀ - 1}`.

`overlapEquations` is the two-element set `{X₀ - C(f), C(f) * X₁ - 1}` in the
relative series algebra over `r₂`. `Overlap` is
`RelativeRelations.QuotientAlgebra` for that set. Thus the closed relation
ideals, carrier types, ring operations, coefficient algebra structures and norms
come from the actual relative series quotients. No carrier or universal
property is supplied as an assumption.

The imported instances make these normed commutative `K`-algebras and
`A`-algebras with ultrametric norms. When `K` is complete, the imported
quotient completeness instance applies.

## Coefficients and displayed variables

`upperBase`, `lowerBase` and `overlapBase` are the imported bounded coefficient
maps. Each includes a coefficient as a constant relative series and applies the
quotient projection (`upperBase_apply`, `lowerBase_apply`, `overlapBase_apply`).
They are contractive for the actual quotient norms (`norm_upperBase_le`,
`norm_lowerBase_le`, `norm_overlapBase_le`).

`upperX`, `lowerY`, `overlapX` and `overlapY` are the quotient images of the
displayed relative variables (`upperX_def`, `lowerY_def`, `overlapX_def`,
`overlapY_def`; `overlapX` uses `X₀` and `overlapY` uses `X₁`). Their norms are
at most one (`norm_upperX_le`, `norm_lowerY_le`, `norm_overlapX_le`,
`norm_overlapY_le`). `norm_one_overlap_le` proves `‖1‖ ≤ 1` in `Overlap`; the
zero quotient is allowed. The generator equations are

\[
\begin{aligned}
\mathrm{upperX}&=\mathrm{upperBase}(f), &
\mathrm{lowerBase}(f)\,\mathrm{lowerY}&=1,\\
\mathrm{overlapX}&=\mathrm{overlapBase}(f), &
\mathrm{overlapBase}(f)\,\mathrm{overlapY}&=1.
\end{aligned}
\]

The corresponding Lean laws are `upperX_eq`, `lowerBase_mul_lowerY`,
`overlapX_eq` and `overlapBase_mul_overlapY`. They follow by projecting the
generating equations and using the algebra-map laws.
`overlapBase_one_mul_overlapX` and `overlapBase_mul_overlapY_fun` restate the
two overlap equations in the exact form required by the imported rational
evaluation: `overlapBase(1) * overlapX = overlapBase(f)` and
`overlapBase(f) * overlapY = overlapBase(1)`.

## Uniqueness of maps out of the quotients

For any normed commutative `K`-algebra `B`, two bounded `K`-algebra maps out of
a quotient are equal when they agree on all coefficient images and on the
displayed variables: `upper_hom_ext` (coefficients and `upperX`),
`lower_hom_ext` (coefficients and `lowerY`) and `overlap_hom_ext` (coefficients,
`overlapX` and `overlapY`). The first two specialize the imported
`RelativeRationalPresentation.hom_ext`. The third combines
`GeneralizedTateAlgebra.relative_hom_ext` with `RelativeRelations.hom_ext`.
No completeness is needed for these statements.

## Constructed arrows

Assume now that `K` is complete. `left : BoundedAlgHom K (Upper K A f)
(Overlap K A f)` evaluates coefficients through `overlapBase` and the
one-variable coordinate at `overlapX`. `right : BoundedAlgHom K (Lower K A f)
(Overlap K A f)` uses the same coefficient map and evaluates its coordinate at
`overlapY`.

Both arrows use the published `RelativeRationalPresentation.evaluate`. This
constructs the convergent relative coefficient sum and descends it through the
closed ideal; it does not assume that the desired map exists. Contractivity of
the coefficient map, the unit-radius coordinate bounds, `norm_one_overlap_le`
and `GeneralizedTateAlgebra.monomialValue_norm_le_weight` supply the monomial
bounds; the bound on `‖1‖` covers the empty monomial. The two overlap equations
show that evaluation annihilates the one-variable relation. The imported descent
then annihilates the closure of the generated ideal. The imported quotient-norm
descent bound gives `norm_left_le` and `norm_right_le`: both arrows are
contractive.

`left_quotientMap` and `right_quotientMap` compute the arrows on representatives
by `GeneralizedTateAlgebra.evaluateCoefficients`. `left_upperBase` and
`right_lowerBase` send each coefficient image to its overlap coefficient image,
while `left_upperX` and `right_lowerY` send the one-variable classes to
`overlapX` and `overlapY`. The structural identities are equalities of bounded
maps:

\[
\mathrm{left}\circ\mathrm{upperBase}=\mathrm{overlapBase},\qquad
\mathrm{right}\circ\mathrm{lowerBase}=\mathrm{overlapBase}.
\]

They are `left_comp_upperBase` and `right_comp_lowerBase`, obtained from the
pointwise coefficient formulas by bounded-map extensionality. Finally, `eq_left`
and `eq_right` show that each arrow is the only bounded map with these
coefficient and variable values.

## Original sources and scope

The retained original Piotr Achinger, *Introduction to non-Archimedean Geometry*
(November 22, 2020), registered as
`achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`, was read
on printed page 6 and pages 63–65. On page 64, Proposition 7.1.1 and the
opening of its proof give the three quotients
`A⟨f⟩ = A⟨X⟩/(X − f)`, `A⟨f⁻¹⟩ = A⟨Y⟩/(fY − 1)` and
`A⟨f, f⁻¹⟩ = A⟨X, Y⟩/(X − f, fY − 1)` and the binary Laurent sequence. Pages 63
and 65 place that sequence in the proof of Tate acyclicity. This module
constructs the objects and arrows only; it does not implement the exactness
proof.

Achinger's page 6 assumes a complete, nontrivially valued scalar field. Here
nontrivial valuation is not needed for the relative series quotients or for
the contractive evaluation and descent that construct the arrows, so it is
dropped. The registered literature-index entry for this source retains the
nontrivial-valuation hypothesis for the source's small-scalar reduction; no
such reduction is used here. No registered errata for this source were found
in the current Library notes or the project literature index.

Vladimir Berkovich, *Non-Archimedean analytic spaces*, Trieste lectures (2009),
registered as `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`, was read
on printed pages 8–9. Definition 2.1.6(i), page 8, gives the relative
restricted series algebra `A{r⁻¹T}` with its weighted Gauss norm; here all
radii are one. Exercise 2.2.2(i), page 9, gives the Laurent quotient equations
`Tᵢ − fᵢ` and `gⱼSⱼ − 1`; with one equation of each kind and unit radii, these
are the overlap equations. Exercise 2.2.2(ii) gives the rational form
`gTᵢ − fᵢ` used by `Upper` (`g = 1`) and `Lower` (`g = f`, numerator `1`).

Taking the closure of the generated ideals is an internal choice: for
affinoid algebras the sources' ideals are already closed, but no closedness
of the plain generated ideal is proved here. Retaining the actual quotient norm,
and proving bounded evaluation and the elementary map laws, are derived
constructions using the published Library interfaces. This unit does not
identify these relative quotients with another scalar presentation. It permits
unit relation ideals, zero or nonreduced bases, nilpotent `f`, and trivial
scalar valuations. It assumes no properness, norm attainment, nonempty
spectrum or injectivity. Exactness, sheafness, finite-module descent, higher
Čech exactness, admissibility and arbitrary-radius descent remain outside this
unit.
