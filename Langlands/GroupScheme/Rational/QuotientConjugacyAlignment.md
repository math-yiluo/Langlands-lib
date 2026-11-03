# Lifting conjugacy witnesses and aligning maximal tori over a quotient

This internal construction records the elementary alignment step needed
in a quotient induction for rational maximal-torus conjugacy. It uses the
existing `SubgroupConjugate`, `IsMaximalTorus` and
`MaximalToriAreConjugate` predicates.

For an arbitrary base scheme and a group-scheme homomorphism
`q : G ⟶ Q`, `points_surjective_of_scheme_section` proves that any
section `s : Q.X ⟶ G.X` of its underlying morphism over the base lifts
points on every test scheme. The lift of `a` is `a ≫ s`, and its
projection is `a` by associativity and the section equation. The proof
requires no compatibility of `s` with multiplication.

`conjugatingDataOverQuotient` takes actual embeddings
`i : H ⟶ G`, `i' : H' ⟶ G`, a proof of rational-point surjectivity
for `q`, and a quotient conjugacy
`SubgroupConjugate (i ≫ q) (i' ≫ q)`. It chooses its rational
conjugating point `a` in `Q`, its source isomorphism `e : H ≅ H'`,
and a rational lift `g` of `a` in `G`. The returned data satisfy

```text
(i ≫ Int(g)) ≫ q = e.hom ≫ (i' ≫ q).
```

The implemented proof uses `innerIso_hom_comp`, which states that an
actual group-scheme homomorphism commutes with conjugation by a point
and its image, then substitutes the lift equation. The accompanying
`conjugatingDataOverQuotient_spec` exposes this exact equation. These
constructions assert alignment of the quotient maps only.

Over every field, `maximalToriAreConjugate_of_quotient` proves conjugacy
upstairs from four explicit inputs:

- rational-point surjectivity of `q`;
- preservation of full maximality for each maximal-torus embedding
  postcomposed with `q`;
- conjugacy of maximal tori in `Q`;
- conjugacy in `G` whenever two maximal tori with the same source have
  equal quotient maps.

The proof applies quotient conjugacy, lifts its point and retains its
source isomorphism using the construction above. It then uses the
published maximality transport lemmas to see that
`i ≫ Int(g)` and `e.hom ≫ i'` are maximal tori in `G` with the
same source and equal quotient maps. The fourth input gives their
conjugacy. Transitivity combines it with conjugation of `i` by `g`
and the source reparametrization by `e`, giving exactly
`SubgroupConjugate i i'`.

`maximalToriAreConjugate_of_quotient_section` substitutes an actual
scheme section for the first input. These are conditional reduction
lemmas: quotient existence, a scheme section, maximality of quotient
images, the residual equal-map case and an induction establishing
quotient conjugacy must still be proved for the intended application.
The module does not prove the full solvable-group theorem.

The provenance is **internal**. The constructions follow directly from
category composition, the published naturality of actual inner
automorphisms, source and ambient maximality transport, and the
published conjugacy relation's transitivity. No external structural
theorem or split-torus conjugacy result is used. The field statements
retain finite and imperfect fields, every characteristic and nonsplit
tori; the general alignment construction also works over an arbitrary
base scheme.
