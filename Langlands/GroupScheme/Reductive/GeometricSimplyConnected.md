# Simply connected and nontrivial geometric fibres under base change

Worker 634.

This internal helper supplies the fibre comparisons needed when applying étale
local splitting to the hypotheses of Conrad's Proposition 6.4.4. It does not
construct a Weil restriction presentation or prove that proposition.

`HasNontrivialPoints G` means that some scheme over the base has a point of `G`
different from the identity. It is equivalent to the full subgroup functor being
different from the identity subgroup functor. It is invariant under actual group
isomorphism and under flat, surjective, quasi-compact base change. The latter proof
uses the published fpqc reflection of trivial subgroup functors, and the elementary
fact that full and identity subgroup functors commute with base change. No
smoothness, affineness or field hypothesis is imposed on this comparison.

`IsFibrewiseSimplyConnected G` means `IsSimplyConnected` on every chosen geometric
fibre. `HasNontrivialGeometricFibres G` means `HasNontrivialPoints` on every such
fibre. Both predicates are preserved by arbitrary scheme base change.

The proof first combines the published arbitrary-field simple-connectedness
ascent with semisimplicity reflection and central-isogeny base change to obtain
an equivalence under field extension. For an actual field-valued point of the
base, `fieldPointFiberIso` identifies the pullback with the residue-field fibre
followed by a field extension. Applying this identification both to the specified
field and to the chosen algebraic closure proves the residue-field and geometric
comparisons. The same route applies to nontriviality using the fpqc comparison.
Composition of actual pullbacks then proves the two arbitrary-base-change results.

These are derived consequences of published Library constructions, rather than
additional source assertions. The motivating source is Brian Conrad, *Reductive
group schemes* (2014), registered as `conrad-2014-reductive-group-schemes`,
Proposition 6.4.4 and its proof, pp.232–233. The point-functor nontriviality condition
agrees with the unchanged affine Weil restriction statement.
