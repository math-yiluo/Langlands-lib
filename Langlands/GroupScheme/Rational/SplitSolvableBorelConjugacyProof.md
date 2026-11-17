# Rational conjugacy of split Borel subgroups

Workers 882 and 755.

`Langlands.GroupScheme.splitSolvableBorelConjugacy.{u}` proves exactly the published `Langlands.GroupScheme.SplitSolvableBorelConjugacyStatement.{u}`. Over every field and for every smooth affine group, every closed split-solvable subgroup lies in a rational conjugate of a given split Borel subgroup, and any two split Borel subgroups are rationally conjugate. The ambient group may be disconnected. The result is uniform in the universe and imposes no characteristic, perfection, or reductivity hypothesis.

The source is James S. Milne, *Algebraic Groups* (2017), Theorem 17.105(a),(b), printed pp.384–385, registered as `milne-2017-algebraic-groups`, SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. The statement and its imports are unchanged. Part (c) on split maximal tori is outside this theorem's scope.

The implementation follows the fixed-coset route of the source's proof of (a), with explicit cocycle descent and a reduction to the identity component:

1. `SplitSolvableFieldCocycle` proves vanishing of cocycles under split-solvable groups over fields. It inducts over the actual finite Ga/Gm quotient series. The elementary cases use additive affine cocycle exactness and split-torus field cocycle vanishing. Each induction step lifts the quotient cochain on a faithfully flat pullback cover, twists into the kernel, and applies induction. Affine refinement extends the result to fppf covers.
2. `SplitSolvableQuotientLifting` pulls back a smooth homogeneous quotient along a rational coset. The differences of the tautological lifts form a cocycle in the subgroup. A trivializing cochain makes a group point compatible under the cover, so effective epimorphism descent gives a rational representative of the coset.
3. `SplitSolvableBorelConnected` constructs the homogeneous quotient of a connected smooth affine group by the given Borel. The Borel is geometrically parabolic, so the published quotient-properness theorem makes this quotient proper and hence pseudo-complete. The published split-solvable fixed-point theorem produces a rational coset fixed by the subgroup. Step 2 lifts it, and the fixed-coset factorization gives the required range inclusion.
4. `SplitSolvableBorelConjugacyReduction` (namespace `Langlands.GroupScheme.SplitSolvableBorelConjugacy`) extends this containment from connected groups to all smooth affine groups by factoring the connected subgroup and Borel through the identity component. It then obtains equality for another split Borel using Borel maximality. This replaces the source's dimension argument for (b).

The entry theorem applies the reduction to the connected containment theorem. Every containment and equality is an assertion about subgroup functors on all relative test schemes; the conjugating points are actual rational points over the original field.

Worker 882 implemented field cocycle vanishing, rational lifting, connected containment, and the final assembly. Worker 755 implemented the identity-component reduction and the maximality argument for the conjugacy clause.
