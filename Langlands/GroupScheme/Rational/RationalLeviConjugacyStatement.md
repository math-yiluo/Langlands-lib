# Rational conjugacy of Levis of a parabolic

Author: Worker 1264.

`RationalLeviConjugacyStatement.{u}` is an unproved proposition over every
field in universe `u`. Let `G` be connected reductive and `j : P → G` an
actual rational parabolic. For two supplied rational Levis `l : L → P`
and `l' : L' → P` and any supplied represented geometric unipotent radical
`r : U → P`, it asserts a unique rational point `q` of `U` for which there
is a group-scheme isomorphism `e : L ≅ L'` satisfying

`l ≫ Int_P(q ≫ r) = e.hom ≫ l'`.

Uniqueness is asserted for the point `q`. The equation concerns actual
group-scheme morphisms, so it identifies the represented subgroup images
on every test scheme, including nonreduced tests. The source isomorphism
is part of the conclusion. The statement preserves the specified radical
and asserts no existence of radicals or Levis. Its hypotheses do not
restrict the field to be split or perfect.

The original source is Borel and Tits, *Groupes réductifs* (1965),
registered as `borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
Corollary 3.14, printed p.80/PDF p.27, states that two rational Levi
subgroups of a connected subgroup of maximal rank are conjugate by a
unique rational element of its unipotent radical. Sections 4.1–4.3,
printed pp.85–86/PDF pp.32–33, specialize this setting to parabolics of
a connected reductive group: standard parabolics contain a maximal
torus, and every parabolic is connected and conjugate to a standard one.
The ambient parabolic hypothesis is essential to this specialization.
The following counterexamples in 3.15, printed pp.80–81/PDF pp.27–28,
show that rational Levi conjugacy cannot be asserted for all groups
merely possessing Levi decompositions.

This is a derived scheme formulation of that parabolic specialization.
The source uses smooth reduced algebraic groups and conjugacy of
subgroups. A proof here must supply the comparison with the specified
geometric radical and the actual source isomorphism, and justify the
equality of scheme morphisms, rather than just equality of rational or
geometric point sets. The published `IsRationalLeviSubgroup` predicate
retains the scheme isomorphism for multiplication with a geometric
unipotent radical. The stronger radical predicate is the one in the
`LeviSubgroup` namespace.

The corrections in Borel–Tits, *Compléments à l'article « Groupes
réductifs »* (1972), registered as
`borel-tits-1972-complements-groupes-reductifs`, SHA-256
`7639a6a59bdb4520ca171fa61c192c000f00396460b05b32766d56dee5a84e49`,
§5, printed pp.274–275/PDF pp.23–24, were inspected:
they contain no correction to 3.14. In particular, the correction at
1965 p.91 concerns the Levi of a parabolic in 4.15, not this conjugacy
assertion.

Defining this proposition proves none of its assertions. It is a
separate structural prerequisite for transporting a centralizer
presentation to a specified rational Levi; split-part centralizer
equality and ambient maximal splitness remain separate obligations.
