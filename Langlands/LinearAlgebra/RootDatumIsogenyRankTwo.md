# Rank-two scaling patterns of root-datum isogenies

This internal derived module isolates the finite Cartan arithmetic needed
when transferring rank-two commutator formulas through a root-datum
isogeny. It does not transfer the group-scheme relations themselves.

For `f : RootDatumIsogeny p P Q`, the exact identity
`rootFactor_mul_pairingIn` states

`q_i * ⟨f(i), f(j)∨⟩ = q_j * ⟨i, j∨⟩`.

Here `q_i = f.rootFactor i`, and the root factors are indexed by the
domain of the weight map. The proof evaluates its transpose identity
on a root and a corresponding coroot, then substitutes the two defining
root-factor equations.

`RankTwoScalingPattern` is a type of concrete alternatives for two
Cartan entries on each side and two natural root factors. The function
`rankTwoScalingPattern` constructs one of those alternatives for two
distinct simple roots of `P` whose images are simple in a supplied base
of `Q`. Its alternatives are:

- Both pairs of Cartan entries vanish; the factors may be independent.
- The two Cartan pairs agree and the two factors agree.
- The pairs `(-1,-2)` and `(-2,-1)` are exchanged. The factor attached
  to the second domain root is twice the first, in that orientation;
  the reverse orientation has the reciprocal relation.
- The pairs `(-1,-3)` and `(-3,-1)` are exchanged, with the same
  orientation convention and ratio three.

The supplied bases and their membership hypotheses are retained
explicitly. The module does not construct a correspondence of bases or
assert a group homomorphism.

The proof first uses the published crystallographic reduced-root
Cartan-pair list. Distinct simple roots have nonpositive pairings, so
only the six pairs `(0,0)`, `(-1,-1)`, `(-1,-2)`, `(-2,-1)`,
`(-1,-3)`, and `(-3,-1)` remain. Case analysis of the two Cartan pairs,
the two positive root factors, and the weighted identities gives the
alternatives. The provenance is this composition of the imported
root-datum results and integer arithmetic, with no additional
classification premise.

The supporting lemma
`characteristicExponent_eq_of_prime_dvd_rootFactor` shows that any prime
dividing a root factor is the characteristic exponent `p`: root factors
are powers of `p`, and `p` is either one or prime.
`characteristicExponent_eq_of_rootFactor_ratio` applies this to a prime
ratio between two factors. Consequently the exceptional ratio two
forces `p = 2`, and ratio three forces `p = 3`. These are assertions
about the root-datum isogeny parameter, without any ring or field
characteristic assumptions.
