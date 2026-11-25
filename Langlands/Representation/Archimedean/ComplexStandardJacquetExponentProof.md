# The exponent shape of Jacquet functionals on complex principal series

Lean module: `Langlands.Representation.Archimedean.ComplexStandardJacquetExponentProof`.

## Result

`Langlands.Archimedean.complexStandardJacquetExponent : ComplexStandardJacquetExponentStatement`.

The statement `ComplexStandardJacquetExponentStatement` (JE) is the Library's, in module
`ComplexStandardHomExponentJacquetReduction`; it is not changed here. For
`d : Fin n → ComplexCharacterData` and a nonzero Jacquet functional `ℓ` on the `U(n)`-finite
functions of `complexStandardModule n (List.ofFn d)` with exponents `a`, `b`, there are a
permutation `σ` and integer vectors `u`, `v`, nonnegative integer combinations of the simple
roots, with `a_j = 2 t(d_{σ j}) + (n - 1) - 2j + (u_j + v_j)` and
`b_j = i (l(d_{σ j}) + u_j - v_j)` for every `j`.

The theorem has no hypotheses beyond those of the statement and uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Proof

The proof is one line: the route theorem `complexStandardJacquetExponentRoute`
(module `ComplexStandardJacquetExponentRoute`, `CO → Trans → Bound → JE`) applied to:

- `complexJacquetCasselmanOsborne : ComplexJacquetCasselmanOsborneStatement`
  (module `ComplexJacquetCasselmanOsborneProof`, with `ComplexGelfandSeparation`);
- `complexJacquetTranslation : ComplexJacquetTranslationStatement`
  (module `ComplexJacquetTranslationProof`, with `ComplexJacquetTranslationMinors` and
  `ComplexJacquetTranslationLift`);
- `complexJacquetAntidominantBound : ComplexJacquetAntidominantBoundStatement`
  (module `ComplexJacquetAntidominantBoundProof`, with `ComplexPartialSqCpowIntegral` and
  `ComplexSphericalJacquet`).

See the Markdown of these modules for the mathematics. In short:
- CO identifies the holomorphic and antiholomorphic coordinates of the exponents as
  permutations of those of `d`, possibly by different permutations.
- Trans moves the exponents by the lowest weight of an exterior power, at the cost of an
  unknown shift of the parameter.
- Bound controls the weights of the parameter in the antidominant chamber.
- The route translates far into the antidominant chamber and compares growth rates, which
  forces the two permutations to agree.

## Provenance

Derived, internal proof of the Library statement JE. The statement is a form of the
classical description of the exponents of Jacquet modules of principal series of `GL_n(ℂ)`. The
route and all its ingredients are proved in the modules listed above.
