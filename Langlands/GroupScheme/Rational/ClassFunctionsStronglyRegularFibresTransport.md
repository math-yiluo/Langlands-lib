# Field transport for strongly regular fibres of the canonical quotient

Authors: Worker 1741, with the geometric core interface and reduction design
agreed with Worker 1531.

This internal development gives the conditional arbitrary-field reduction for
the exact canonical strongly regular fibre statement. It takes an algebraically closed geometric core and the separately specified
field base-change theorem as inputs. Both inputs remain explicit hypotheses of
`stronglyRegularFibres_of_algClosed`; neither is asserted as proved here.

The quotient helpers use the fourth compatibility equation of
`FieldBaseChangeStatement` and the actual pullback adjunction on scheme points.
They preserve equality of images under the fixed canonical map `rho`.

The centralizer helper transports the original all-test condition to arbitrary
tests after a change of base. A commutative closed subgroup containing the
centralizer represents that centralizer, and the published representation and
point-centralizer base-change laws give the result. It imposes no reducedness
or field-valued restriction on the tests.

The definitions in `StronglyRegularFibresTransport` construct the actual
algebraic-closure cover `q : Spec (AlgebraicClosure F) → Spec F` over `Spec K`,
the comparison of its canonical structure morphism with the composite through
`F`, the extended points of the sequential base change, and the projection of
its points back to points of `G`. The projection respects the exact point
pullback and conjugacy equations.

`stronglyRegularFibres_of_algClosed` applies the geometric core to
`(G_F)_(AlgebraicClosure F)`. Semisimplicity passes through both field extensions
by the published arbitrary-extension theorem. The proof applies the quotient
comparison first for `K → F` and then for `F → AlgebraicClosure F`, and pulls back
the supplied closed torus and its represented point centralizer. The resulting
conjugator projects to the exact equation required by
`StronglyRegularFibresStatement`.

The reduction preserves the arbitrary universe `u`, arbitrary fields `K` and
`F`, the actual canonical `rho`, the all-test centralizer containment and the
absence of extra hypotheses on `y`. The output field is the algebraic closure
of `F` in the same universe. The algebraically closed input is displayed
explicitly: it assumes semisimplicity and the supplied toral centralizer, and
asserts conjugacy over that algebraically closed field. Its independent proof
and the proof of `FieldBaseChangeStatement` are still required before an
unconditional closing theorem can be obtained.

Provenance: these are routine internal consequences of the published pullback,
centralizer, semisimple field-extension and quotient interfaces. The
algebraically closed assertion is an input, not a new theorem in this pair.

This definition contribution groups the algebraic-closure cover and point
constructions with their routine correctness lemmas. The accompanying
`ClassFunctionsDynamicLimits` pair supplies the small canonical-quotient limit
adapters used by the same geometric reduction. The selected definition is
`StronglyRegularFibresTransport.algebraicClosureCover`; the conditional reduction
is a supporting theorem. This contribution does not discharge the task's exact
proof target or establish either of its two mathematical inputs.

The selected `algebraicClosureCover` interface is a transparent alias of the
existing `QuasiSplitRegularConjugate.algebraicClosureCoverPoint`, now housed in
[AlgebraicClosureCover](AlgebraicClosureCover.md). The shared construction retains
its original map and scalar-tower proof.
