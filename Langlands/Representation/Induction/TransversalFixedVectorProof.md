# Fixed vectors over an arbitrary double-coset transversal (Renard III.2.2)

`Langlands.Induction.inducedFixedVectorTransversal` proves exactly the published
`InducedFixedVectorTransversalStatement`, with independent universe parameters
`uR`, `uG`, and `uV`. For any compact open subgroup `K` and any supplied double-coset
transversal `Ω`, evaluation is a linear equivalence from the `K`-fixed vectors of
smooth induction to all families of coefficient fixed vectors on `Ω`, and from
the `K`-fixed vectors of compact induction to the dependent finitely supported
families `Π₀ ω : Ω, fixedVectors σ (conjOpenSubgroup P K ω).toSubgroup`.
Both equivalences have the asserted evaluation formula.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
III.2.2 Lemma and (III.2.2.1), printed pp.71–72 / PDF pp.77–78.
The Lean statement generalizes the source's smooth complex representation of a
closed subgroup in a totally disconnected group: the proof works for any
representation of any subgroup of a topological group over a commutative ring.
It adds no hypothesis to the published statement, and places no finiteness
condition on `Ω` or on the double-coset space.

For smooth induction, the private linear map `transversalEvaluation` evaluates
at each representative; `eval_mem_fixedVectors` gives the required coefficient
stabilizer. Covariance and right `K` invariance show that a value at `p * ω * k`
is determined by the value at `ω`, proving injectivity using the covering
hypothesis. For surjectivity, `transversalQuotientEquiv` identifies `Ω` with the
entire double-coset quotient, using both covering and distinctness. Given a
family of coefficients, attach the published `fixedDoubleCosetSection` to each
representative, and define the new function at `x` using the section indexed by
the double coset of `x`. Left multiplication by `P` and right multiplication by
`K` preserve that class. The resulting function is covariant and right
`K` invariant, so `smoothFunctionOf` bundles it as a smooth induced function.
The section's value at its own representative proves the prescribed evaluation.
This is pointwise gluing, with no infinite sum.

For compact induction, `compactTransversalEvaluation_finite` covers the actual
projected nonzero support by the open images of `ωK` in the left quotient `P \ G`.
Compactness gives a finite subcover. If evaluation at a representative is
nonzero, its quotient point lies in one of these images; the resulting
double-coset equality and distinctness place that representative in the finite
subcover. Thus evaluation defines `compactTransversalEvaluation` with values in
`DFinsupp`. Its injectivity follows from smooth injectivity after forgetting
compact support. `compactTransversalSection` bundles the published compact
one-double-coset section at an arbitrary `ω`. Its evaluations form exactly
`DFinsupp.single ω v`: the own-coordinate identity and vanishing on distinct
double cosets are the published `fixedDoubleCosetSection_eval_self` and
`fixedDoubleCosetSection_eval_of_ne`. Evaluation injectivity then proves linearity
of the section in its coefficient. `DFinsupp.lsum` forms the finite section sum,
and `DFinsupp.lhom_ext` reduces its right-inverse identity to the single-section
identity. Finally, `LinearEquiv.ofBijective` gives both equivalences; their
forward evaluation formulas hold by definition.

The private helpers are derived proof infrastructure. The compact part adapts
the published `CompactFixedVectorModel` construction from Mathlib's chosen
representatives to the supplied transversal; the smooth part extends the
published finite-transversal `FixedVectorModel` argument by the pointwise gluing
above. Compactness of `K` is used through the published one-double-coset
sections, while compactness of the function's actual quotient support supplies
the finite evaluation family. No change of the target statement or its imported
modules is needed.
