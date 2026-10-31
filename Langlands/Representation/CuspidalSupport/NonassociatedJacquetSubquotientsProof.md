# Nonassociated Jacquet modules have no nonzero quasicuspidal subquotients

Authors: Workers 169 and 191.

`Langlands.CuspidalSupport.nonassociatedJacquetSubquotients.{uF,uV}`
proves the existing
`Langlands.CuspidalSupport.NonassociatedJacquetSubquotientsTheorem.{uF,uV}`
for every prime, actual finite p-adic extension `F`, supplied compatible
topological data `T`, and natural rank `n`. The field and inducing carrier
universes are independent. The theorem applies to any smooth complex
quasicuspidal inducing representation of the source block Levi.
If the source and target Levis are not associated, every quasicuspidal
smooth subquotient of the actual normalized Jacquet module of its normalized
induction has a subsingleton carrier.

The input representation has carrier universe `uV`; the Jacquet module and
its quantified subquotients have carrier universe `max uF uV`, as in the
unchanged statement. The theorem has no extra premise. It adds no
admissibility, irreducibility, length or dimension restriction.

At rank zero the published elementary association helper proves the result:
the two embedded Levis are associated in the trivial matrix group, so the
negative hypothesis is impossible. The remaining argument uses `0 < n`.

At positive rank, specialize the published unconditional theorem
`Langlands.Geometric.padicGeometricLemma`. Unpack its source and target
refinements, all actual intersection identifications, exhaustive enumeration,
gluing permutation and finite natural filtration. Evaluate that filtration
at the inducing representation using `objectFiltrationAt`. This produces an
actual zero-to-full object filtration with the same consecutive quotients.

For each graded quotient, choose the actual smooth geometric piece supplied
by `geometricPieceSmoothFunctor`. Its underlying representation is proved
equal to the corresponding `geometricPieceFunctor` value. Composing that
equality with the evaluated natural graded isomorphism gives the
representation equivalence required by the published finite-filtration
criterion `padicLeviFiltrationNoQuasicuspidalSubquotients`.

Split according to whether the source refined parabolic is full.
If it is proper, quasicuspidality kills its actual unipotent coinvariants.
The published zero-piece helper propagates this through the conjugation
transport and normalized induction. Thus the smooth geometric piece is
zero, and `subsingleton_of_isSubquotient` makes every actual subquotient zero.
If the source refined parabolic is full, the subgroup comparison
`target_refinement_proper_of_nonassociated_source_full` proves that the
target refined parabolic is proper. Here the hypothesis is nonassociation
of the two whole Levis. Apply the published unconditional theorem
`padicProperRefinedInduction` to that target refinement and the actual
smooth inducing object `geometricPieceInducingFunctor`. The smooth
geometric piece is definitionally this normalized refined induction, so
every quasicuspidal subquotient is zero. The finite-filtration criterion
then gives the same conclusion for the entire Jacquet module.

This is an internal final deduction from published geometric, subgroup,
smooth-piece, proper-induction and finite-filtration proofs. Worker 169
supplied the subgroup dichotomy and final filtration assembly; Worker 191
supplied the evaluated-filtration, zero-carrier, smooth-piece and
proper-target assembly work incorporated here. The geometric lemma and
proper induction are imported proved theorems, with no theorem-valued
input. No private draft is imported. The target's Lean/Markdown pair and
all imported pairs are unchanged.

The motivating original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), Corollary 2.13(b),
printed p.449 / PDF p.10, with sections 2.4(a),(d) and 2.12 supplying
the proper-induction and geometric-filtration route. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original passage was read directly. The implemented proof uses the
published actual finite-filtration criterion to make its subquotient
propagation explicit.
