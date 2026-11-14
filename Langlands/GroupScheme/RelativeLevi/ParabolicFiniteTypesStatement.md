# Statement: finitely many parabolic types on an étale neighbourhood

Worker 655, Task 6339.

`Langlands.GroupScheme.RelativeParabolicEtaleLocalFiniteTypesStatement.{u}`
is an unproved proposition definition. It isolates the finite classification
used in constructing the scheme of parabolic subgroups; it does not construct
that scheme.

For every reductive group scheme `G` over an arbitrary scheme `S` and every
point `s`, the statement asks for an affine étale neighbourhood
`f : Spec R ⟶ S` whose image contains `s`. Over this neighbourhood there are
finitely many actual relative parabolic inclusions
`j a : P a ⟶ G_R`, indexed by `Fin n`. Each satisfies the unchanged published
predicate `IsRelativeParabolicSubgroup`: its source is smooth and affine, the
inclusion is monic, and every residue fibre is parabolic. No closedness premise
is added to that predicate.

For every field `k` in the same universe, every point `x : Spec k ⟶ Spec R`,
and every field parabolic `i : Q ⟶ (G_R)_k`, there is exactly one index `a`
such that `i` is conjugate to the pullback of `j a` by a rational point of
`(G_R)_k`. The rational conjugating point may depend on `i` and `x`; its
uniqueness is neither asserted nor expected. Conjugacy is equality of subgroup
functors on **every** test scheme over `Spec k`, after composition with the
actual `innerIso`. The statement does not replace this equality by equality of
sets of rational points.

The comparison uses the actual iterated base change `(G_R)_k`. It therefore
does not silently identify that object with the pullback of `G` along `x ≫ f`.
Every `k`, `x`, `Q`, and `i` is quantified after the fixed finite family has
been chosen. Thus the same family works over all field extensions and at all
points of the neighbourhood. No field, base point, or parabolic is selected
in advance when choosing the finite family.

The source is Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The relevant argument is the proof of Corollary 5.2.9 on p.157, together with
the discussion preceding that proof; PDF page numbers agree with printed
pages. Conrad first passes étale-locally to a split maximal torus and then
Zariski-locally to a constant split root datum. A positive system determines a
finite family of cocharacters, indexed by the parabolic subsets containing
that positive system. Their dynamic parabolics are representatives without
repetition for parabolic conjugacy types. These parabolics are defined over
the neighbourhood and remain standard parabolics over every field-valued
point.

The rational-point formulation over `k` uses the split case of the classical
classification: standard parabolics in a split reductive group represent the
rational conjugacy classes as well as the geometric types. Conrad's
Corollary 5.2.7 and the paragraph preceding Corollary 5.2.9 on pp.155–157
explain the relative conjugacy and quotient interpretation. The present
statement is a derived consequence of this source route, rather than a
verbatim numbered assertion.

This result is a prerequisite for assembling finitely many smooth proper
homogeneous quotient charts. It supplies neither a universal parabolic over
such a quotient nor a representation on arbitrary test schemes, a line
bundle, or an effective descent theorem. In particular, a proof of this
proposition alone would not prove `RelativeParabolicSchemeStatement`.

The separate published `RelativeParabolicEtaleLocalConjugacyStatement`
starts with two supplied relative parabolics and a conjugacy over one residue
field. It does not choose a finite family or classify field parabolics.
Conversely, the present statement classifies the field-valued fibres and does
not itself promote fibre conjugacies to étale-local conjugacies of families.
