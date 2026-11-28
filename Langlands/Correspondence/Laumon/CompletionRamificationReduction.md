# Ramification across the completion, from the Galois comparison

The module `Langlands.Correspondence.Laumon.CompletionRamificationReduction` proves

- `henselianCompletionRamification_of_galois`: `HenselianCompletionGaloisStatement` implies
  `HenselianCompletionRamificationStatement` (both in
  `Langlands.Correspondence.Laumon.Completion`), in the same universe `u`.

For a finite field \(k\), the hypothesis gives that `completionRestriction k` is a homeomorphism
\(r\), and the six clauses of the conclusion are, in order:

1. `absoluteInertia_map_completionRestriction` (uses the surjectivity of \(r\)),
2. `exists_constants_residue_equiv`,
3. `completionRestriction_localProjection_pow`

of `Langlands.Correspondence.Laumon.CompletionConstants`;

4. `mem_map_localWildInertia_iff` of `Langlands.Correspondence.Laumon.CompletionWildInertia`;

5. `mem_lowerRamificationGroup_iff_henselianLowerTest` and
6. `mem_map_localAbsoluteUpperRamificationGroup_iff`

of `Langlands.Correspondence.Laumon.CompletionLowerGroups`. Clauses 2 and 3 do not use the
hypothesis. The theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
