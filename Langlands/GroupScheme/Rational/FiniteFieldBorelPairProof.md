# Borel pairs over finite fields

Workers 881 and 308.

`Langlands.GroupScheme.finiteFieldBorelPair.{u}` proves the unchanged published
`Langlands.GroupScheme.FiniteFieldBorelPairStatement.{u}` for every universe.
For every finite field and every smooth connected affine group over it, a
geometric Borel subgroup contains an ambient maximal torus, and any two such
pairs are conjugate by one rational point. The equalities are equalities of
subgroup functors on all schemes over the field.

The target is Milne, *Algebraic Groups* (2017), Proposition 17.99, printed
pp.383–384 (registered source `milne-2017-algebraic-groups`). The
[statement documentation](FiniteFieldBorelPairStatement.md) records the exact
source correspondence and the corrections needed in the printed proof. The
implemented proof uses the following route through published Library results.

1. [Borel-pair existence](FiniteFieldBorelPairExistence.md) first descends a
   Frobenius invariant geometric Borel. The finite-field geometric maximal-torus
   theorem gives a torus in it. Absolute Borel maximal-torus existence and
   conjugacy of maximal tori inside a smooth connected solvable group show
   that the chosen torus is maximal in the ambient group after extension to the
   algebraic closure. Reflection gives its ambient maximality over the original
   field.
2. [Rational Borel conjugacy](FiniteFieldBorelPairConjugacy.md) corrects an
   algebraic-closure conjugator using Lang's theorem in the source Borel.
   The Frobenius discrepancy normalizes that Borel, so Borel self-normalization
   puts it in the Borel itself. The corrected point is Frobenius fixed and
   descends exactly to a rational point. Faithfully flat range descent gives
   the required rational Borel range equality.
3. [Pair assembly](FiniteFieldBorelPairAssembly.md) factors the transported
   first torus and the second torus through the target Borel. Rational conjugacy
   of maximal tori in smooth connected solvable groups supplies a point of that
   Borel conjugating the two factorizations. Its image times the Borel
   conjugator conjugates both ranges simultaneously.

The [point and Galois transport helpers](FiniteFieldBorelConjugacy.md) provide
exact recovery of Frobenius-fixed affine points and naturality of the subgroup
transport used in step 2. These helper modules are internal derived results for
this proof. The final theorem combines existence with steps 2 and 3 and
introduces no further hypotheses.
