# Reduction of adic lifting to infinitesimal lifting and adic Hom comparison

This internal result assembles the proof route of SGA 3, Exposé IX,
Corollaire 7.3 (Gille–Polo recomposed edition, 2009, p.59, original margin
p.72; registered source `sga3-expose-ix-gille-polo-2009`).

`RelativeMultiplicativeType.etaleSurjectiveFppfCover` regards an actual
étale surjection as a singleton fppf cover. Étaleness supplies flatness and
local finite presentation; surjectivity supplies the covering condition.
`isMultiplicativeType_of_etale_surjective` therefore shows that a group
diagonalizable on this cover satisfies the Library's relative
multiplicative-type predicate. No finiteness hypothesis is needed for
this bridge.

`multiplicativeTypeAdicLift_of_infinitesimal_of_homComparison` proves the
exact published `MultiplicativeTypeAdicLiftStatement` from two explicit
proposition inputs in the same universe:

- `MultiplicativeTypeInfinitesimalLiftStatement`, the lifting and
  kernel-conjugacy theorem for nilpotent thickenings.
- `MultiplicativeTypeAdicHomComparisonStatement`, bijectivity of global
  Hom restriction to actual compatible adic systems for isotrivial
  multiplicative-type sources and affine targets.

For each ring, ideal, and pair of group schemes in the target statement,
the finite étale splitting witness gives the multiplicative-type
hypothesis by the singleton-cover bridge. The surjectivity part of Hom
comparison and the infinitesimal lifting recursion lift the prescribed
homomorphism. Its injectivity part and the infinitesimal conjugator
recursion give the conjugacy of any two lifts by a global point reducing
to the identity. Finally `I^(0+1) = I` identifies the level-zero quotient
with the target's exact quotient map.

The implemented recursions use actual group-scheme homomorphisms,
canonical pullback comparisons, and actual points. The conjugator
construction lifts a point through each square-zero adic transition,
corrects it by an infinitesimal conjugator with identity reduction, and
algebraizes the compatible points using affineness and completeness.
There are no additional assumptions on the target statement.

This file proves a conditional reduction. It does not prove either of
the two input propositions, so it does not by itself give an
unconditional proof of `MultiplicativeTypeAdicLiftStatement`.
