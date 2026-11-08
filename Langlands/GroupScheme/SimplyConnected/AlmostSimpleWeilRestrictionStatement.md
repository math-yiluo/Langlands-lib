# Simply connected almost-simple groups as Weil restrictions

Author: Worker 1783.

`Langlands.GroupScheme.SimplyConnectedAlmostSimpleWeilRestrictionStatement`
is a closed `Prop`-valued definition at arbitrary universe `u`. For every field
`k : Type u` and group scheme `G` over `Spec k`, with affine structure morphism,
`IsSimplyConnected G` and `IsAlmostSimple G`, it asserts the existence of:

- a field `K : Type u`, an algebra structure over `k`, and instances of
  `FiniteDimensional k K` and `Algebra.IsSeparable k K`;
- a group scheme `G'` over `Spec K` with affine underlying scheme and locally
  of finite type structure morphism, satisfying `IsSimplyConnected G'` and
  `IsAbsolutelyAlmostSimple G'`;
- an isomorphism `G ≅ AffineWeil.groupScheme k K G'`.

All objects are the published Library objects, together with the definition
`IsAbsolutelyAlmostSimple` in `Reductive.AbsolutelyAlmostSimple`. The
isomorphism is enclosed in `Nonempty`, so the entire assertion is a proposition;
no group, field, isomorphism or proof of the assertion is constructed here.

The principal source is Borel–Tits, *Groupes réductifs* (1965), registered
`borel-tits-1965-groupes-reductifs`, 6.17–6.21, printed pp.111–113 /
PDF pp.58–60, especially 6.21(ii), printed p.113 / PDF p.60. Their general
almost-simple semisimple group is isogenous to a restriction of scalars of
a group almost-simple over the algebraic closure. The finite separability
of the field of definition is explicit in their argument.

The isomorphism and simple connectedness of the factor are the simply
connected refinement of that assertion. Milne, *Algebraic Groups* (2017),
registered `milne-2017-algebraic-groups`, Theorem 24.3 and its preceding
discussion, printed pp.512–513 / PDF pp.528–529, give this form directly.
For a simply connected semisimple group the multiplication of its geometric
almost-simple normal factors is an isomorphism, rather than merely the
central isogeny available in general. The factors are simply connected:
an incoming central cover of one factor, multiplied by the other factors,
would otherwise give a nontrivial incoming central cover of the product.
Almost-simplicity over `k` makes the Galois action on these factors
transitive. The stabilizer of one factor gives the finite separable field
`K`; descending the factor and the product decomposition gives the indicated
Weil restriction and isomorphism. This explains why no further isogeny
replacement is necessary. The relevant comparison is a central isogeny;
simple connectedness is not being used to invert arbitrary inseparable
isogenies. Milne's official errata, registered
`milne-2017-algebraic-groups-errata-2026-11-02`, entry for p.513, explicitly
correct “isogeny” to “central isogeny” in the preceding discussion.

The terminology “absolutely almost-simple” follows Milne, Definition 19.7
and Notes, printed p.399 / PDF p.415, with the official p.399 correction
used by the published `IsAlmostSimple`. The geometric clause uses the
almost-simple branch consistently despite the reversed parenthetical
ordering in the printed definition.

The remaining formulation choices are explicit. Both fields lie in
`Type u`; a finite extension admits a model in that universe, and no chosen
embedding in a fixed closure is required in the conclusion. The affine
and locally of finite type witnesses for `G'` make the existing
`AffineWeil.groupScheme` construction available; they are properties of
the resulting semisimple group, not extra premises on `G`. No uniqueness
of `K`, of the factor, or of the isomorphism is asserted. The statement
has arbitrary characteristic and imposes no perfectness, infinitude,
local-field or topology hypothesis. These are formulation explanations,
not Lean proofs of the structural assertion.
