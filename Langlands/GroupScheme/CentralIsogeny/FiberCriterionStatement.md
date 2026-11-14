# Statement: the reductive fibre criterion for central isogenies

Worker 673.

`Langlands.GroupScheme.ReductiveCentralIsogenyFiberCriterionStatement.{u}`
is a `Prop`-valued statement with no proof in this module.

Let `S` be any scheme, let `G` and `H` be reductive `S`-groups, and let
`f : G ⟶ H` be surjective on underlying scheme points. The statement says
that `f` is a central isogeny if and only if, for every point `s` of `S`,
the actual scheme-theoretic kernel of its pullback along
`geometricPoint S s : Spec κ(s)^alg ⟶ S` is finite over that algebraically
closed field and its inclusion in the source fibre is central.

The predicates are those of `Reductive.Basic` and `CentralIsogeny.Basic`.
`IsCentralIsogeny f` asserts a finite, flat, surjective and locally finitely
presented map, with central full scheme-theoretic kernel.
`IsCentral` is an all-test-scheme condition, including all restrictions of
test points. `IsFinite (kernel f_s).X.hom` is finiteness of the kernel's
structure morphism. Neither reduced kernels nor merely central rational
points suffice for the statement.

The source is Brian Conrad, *Reductive group schemes* (2014), source ID
`conrad-2014-reductive-group-schemes`, retained as
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Printed and one-based PDF page numbers agree. Definition 3.3.9 and
Proposition 3.3.10, p.103, give the isogeny convention and exactly the
finite-central-kernel criterion for surjective homomorphisms between
reductive groups over a scheme.

This formulation uses the fixed geometric point above each point of `S`.
The source's fibre criterion has the same meaning: kernel formation commutes
with base change, and finiteness and centrality can be checked after the
faithfully flat field extension from `κ(s)` to its algebraic closure.
These comparisons are part of the proof obligation, not assumptions.
The extra local-finite-presentation clause in the Library's isogeny
predicate follows because reductive groups are smooth and affine, hence
finitely presented over `S`, and their `S`-morphisms are locally finitely
presented.

Both reductivity hypotheses and the explicit surjectivity hypothesis are
retained. No finiteness, connectedness, reducedness or Noetherian hypothesis
is placed on `S`, and the empty base is allowed. The statement does not
assert the analogous finiteness result for arbitrary smooth groups with
noncentral kernels.
