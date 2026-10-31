# Vanishing of the Jacquet module when no target refinement is associated

Authors: Workers 169 and 191.

`Langlands.CuspidalSupport.quasicuspidalJacquetVanishing.{uF,uV}` proves the
existing
`Langlands.CuspidalSupport.QuasicuspidalJacquetVanishingTheorem.{uF,uV}`
for every prime, actual finite p-adic extension `F`, supplied compatible
topological data `T`, and natural rank `n`. The field universe `uF` and
inducing carrier universe `uV` are independent. The input is any smooth
complex quasicuspidal representation of the source block Levi.

The hypothesis says that no standard block refinement of the target Levi,
embedded in the ambient general linear group, is associated to the source
Levi by a permutation matrix. Under that hypothesis the actual normalized
Jacquet module of normalized induction has a subsingleton carrier, hence
is zero. The carrier of this result lies in `Type (max uF uV)`.
The theorem has no extra premise, admissibility, irreducibility, length
or dimension restriction. Its negative hypothesis is the one in the
unchanged companion statement; it is kept distinct from nonassociation
of the two whole Levis used in `NonassociatedJacquetSubquotientsTheorem`.

The proof first separates rank zero. The published rank-zero helper
constructs the empty target refinement and its association in the trivial
matrix group. This contradicts the negative hypothesis, proving the
zero-rank statement. At positive rank, specialize the published
unconditional theorem `Langlands.Geometric.padicGeometricLemma`.
Its witnesses give source and target refinements with the actual
intersection identifications, an exhaustive enumeration of minimal
representatives, a gluing permutation, and a finite natural filtration.

Evaluate that filtration at the input representation using
`objectFiltrationAt`. The result is an actual zero-to-full object
filtration of the Jacquet module with definitionally the same graded
quotients. For each index, the subgroup comparison
`source_refinement_proper_of_no_associated_refinement` forces the
corresponding source refined parabolic to be proper. Quasicuspidality
therefore kills the actual unipotent coinvariants of the source
representation. The published helper
`geometricPieceFunctor_subsingleton_of_proper_source` propagates this
zero carrier through the actual conjugation transport and normalized
induction.

The geometric lemma's natural graded isomorphism, evaluated at the input
representation, identifies the actual graded quotient with that zero
piece. Its underlying linear equivalence is injective, so the quotient is
subsingleton. Finally the published theorem
`Langlands.objectRepFiltrationSubsingleton` propagates vanishing of all
successive quotients to vanishing of the whole Jacquet module.

This is an internal final deduction from the published geometric lemma,
subgroup comparison, zero-piece and finite-filtration proofs. Worker 169
supplied the subgroup comparison and final assembly; Worker 191 supplied
the evaluated-filtration and zero-carrier work incorporated here. The
geometric lemma is an imported proof, with no theorem-valued input.
No private draft is imported. The target's Lean/Markdown pair and all
imported pairs are unchanged.

The original mathematical source is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), Corollary 2.13(a),
printed p.449 / PDF p.10, using the geometric lemma in section 2.12 and
the quasicuspidal vanishing condition of section 2.4. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original passage was read directly. The implemented proof makes the
finite-filtration vanishing step explicit using the published criterion.
