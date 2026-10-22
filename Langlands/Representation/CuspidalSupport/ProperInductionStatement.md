# Proper parabolic induction has no quasicuspidal subquotients

`Langlands.CuspidalSupport.PadicProperRefinedInductionTheorem` states
Bernstein–Zelevinsky 2.4(d) in the equivalent form supplied by 2.4(a), for
the actual product Levis of GL. It is a proposition definition, with no proof
of the representation-theoretic assertion.

## Exact statement

Fix a prime `p`, an actual finite extension `F : PadicField p` of the p-adic
field, compatible `TopologicalData T`, a positive integer `n`, and an ordered
positive block shape `B : BlockShape n`. The ambient group is
`M = B.Levi F.Carrier` with its product topology from `T.topology`.

`ProperRefinedInductionTheorem T B` says the following. For every standard
refinement `S : BlockRefinement B` such that the actual subgroup
`refinedParabolic F.Carrier B S` is not the whole product Levi, every smooth
complex representation `A` of `refinedLevi F.Carrier B S`, and every smooth
complex representation `D` of `M`, if

- `D` is an actual smooth subquotient of
  `(T.normalizedRefinedInductionFunctor B S).obj A`, and
- `D.representation` satisfies the existing `IsLeviQuasicuspidal B`,

then `Subsingleton D`. For a module this is exactly that its underlying
vector space is zero.

The induction functor is the one constructed in `Geometric.RefinementFunctors`:
inflate along the actual refined Levi projection, multiply the inducing action
by the positive half modulus, and use the smooth covariant function space with
right translation. It is not a supplied functor variable.
`SmoothRep.IsSubquotient` is the Library's factorization through an actual
smooth subrepresentation and quotient. Quasicuspidality is vanishing of the
actual unipotent coinvariant module for every proper standard refinement of
`M`. No admissibility, irreducibility, or finite-length condition is imposed
on either `A` or `D`.

The field universe `uF` and inducing carrier universe `uV` are independent.
The inducing representation has carrier in `Type uV`; the induced function
space and `D` have carriers in `Type (max uF uV)`.
`PadicProperRefinedInductionTheorem` universally quantifies over the prime,
field, compatible topology, positive rank, and outer block shape.

## Relation to the source

The source is I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups I*, Annales scientifiques de l'École Normale Supérieure
(4) 10 (1977), 441–472, registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 2.4, printed pages 446–447 (PDF pages 7–8), defines quasicuspidality.
Part (a) decomposes each smooth representation as a quasicuspidal summand
and a complementary summand with no nonzero quasicuspidal subquotients.
Part (d), printed page 447, says that the quasicuspidal summand of a
representation induced from a proper standard Levi is zero.

In the decomposition from (a), vanishing of the quasicuspidal summand means
the whole representation is isomorphic to the complementary summand, so it
has no nonzero quasicuspidal subquotients. Conversely, if there are no such
subquotients, the quasicuspidal summand, being a subrepresentation, is zero.
This explains the formulation used here; the Lean module does not prove this
equivalence or assume (a) as an input. The independent statement of (a) remains
in `QuasicuspidalStructureStatement`.

Sections 2.1–2.3, printed page 446 (PDF page 7), identify standard subgroups
of GL with products of GL groups and their standard subgroups with ordered
subpartitions. Thus the source's ambient reductive group can be the product
Levi `M`, and its proper standard Levi is the actual refinement in the Lean
statement. Sections 1.8 and 2.3 prescribe the positive half normalization
and identify compact and smooth induction for these parabolics.

The original proves (d) from normalized adjunction in 2.3(b) and the vanishing
of the proper Jacquet module of the quasicuspidal summand. That argument and
the compactness and modulus identifications are future proof obligations.
The statement is specialized to characteristic-zero p-adic fields and complex
coefficients; it does not claim the theorem for every reductive group or every
coefficient field.
