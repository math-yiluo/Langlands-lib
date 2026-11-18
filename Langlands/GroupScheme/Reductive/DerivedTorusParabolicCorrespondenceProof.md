# Maximal tori and parabolic subgroups of a reductive group and its derived group

`Langlands.GroupScheme.reductiveDerivedTorusParabolicCorrespondence` proves the
unchanged published
[`ReductiveDerivedTorusParabolicCorrespondenceStatement`](DerivedTorusParabolicCorrespondenceStatement.md)
in every universe `u`. The base is an arbitrary scheme, and the theorem retains
exactly the statement's hypotheses on the reductive group, the derived-group
inclusion, its supplied torus quotient, and the maximal central torus.

Intersection with the derived group sends maximal tori to maximal tori and
relative parabolic subgroups to relative parabolic subgroups. Every such
subgroup of the derived group arises by intersection. The inverse is realized
by multiplication with the maximal central torus, factoring through an
isogeny onto the ambient maximal torus or a central isogeny onto the ambient
parabolic. The corresponding multiplication maps onto an original torus or
parabolic are also isogenies of the stated kind. Equal intersections imply
equal subgroup-functor ranges in the ambient group.

The implemented proof applies
[`reductiveDerivedTorusParabolicCentralProductReduction`](DerivedTorusParabolicCentralProductReduction.md)
to the published unconditional theorem
[`reductiveDerivedCentralIsogeny`](DerivedCentralIsogenyProof.md).
The latter supplies the actual central multiplication isogeny
`Z ⊗ D → G`. The reduction assembles the relative maximal-torus intersection
and extension constructions and the relative parabolic intersection and
descent constructions. Reconstruction from their multiplication
factorizations supplies both injectivity clauses.

This is an internal composition of published results. All premises of the
reduction are discharged, and the conclusion is the original proposition
with no additional hypotheses. The imported statement and its dependencies
are unchanged. The statement's source is Conrad's *Reductive group schemes*
(2014), Proposition 5.3.4; its paired Markdown records the source and encoding.
Worker 715 assembled this final proof from the torus and parabolic support
developed with Worker 680.
