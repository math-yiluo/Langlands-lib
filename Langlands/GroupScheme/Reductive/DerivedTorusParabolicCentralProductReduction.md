# Derived torus and parabolic correspondence from the central-product isogeny

This internal reduction states that `ReductiveDerivedCentralIsogenyStatement`
implies the unchanged `ReductiveDerivedTorusParabolicCorrespondenceStatement`
in every universe. The former statement remains a premise; this module does not
assert its unconditional proof.

For fixed data satisfying the original target's hypotheses and a supplied
central-product isogeny `Z ⊗ D ⟶ G`, the helper
`DerivedCorrespondence.geometricClauses_of_centralProduct` assembles the four
geometric clauses. The full intersection of a relative maximal torus with `D`
is a relative maximal torus by `relativeDerivedMaximalTorusIntersection`.
The actual central-product restriction gives the required isogeny onto the
original torus. Conversely, `RelativeDerivedTorus.exists_extension` supplies
an ambient maximal torus, its product isogeny and the full intersection equality.
For relative parabolics, `CentralProductParabolic` supplies the analogous
intersection, restricted central isogeny and inverse construction over the
original base scheme.

The final theorem takes a relative-torus quotient from the original
correspondence hypotheses and specializes the supplied central-isogeny statement
to it. Its product-isogeny component discharges the helper's remaining premise.
`DerivedCorrespondence.correspondence_of_geometric_clauses` then supplies both
injectivity clauses by reconstruction from the product factorizations. Thus
the conclusion has exactly the published target's quantifiers and hypotheses;
no base restriction or additional assumption is inserted into that conclusion.

The provenance is internal composition of the relative intersection, extension,
central-product restriction and represented-subgroup reconstruction results.
The statement modules of both statements, `DerivedCentralIsogenyStatement` and
`DerivedTorusParabolicCorrespondenceStatement`, are imported without change.
