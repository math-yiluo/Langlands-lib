# The enveloping action preserves cuspidality

For a cuspidal finite-smooth rational-invariant function, the smooth maximal-block constant-term slice at any fixed finite adelic argument is zero. The derivative of that zero slice in every real Lie direction is zero. The Library's `smoothDifferential_smoothConstantTermSlice` identifies this derivative with the corresponding constant term of the genuine Lie derivative. Evaluating at the infinite component of an arbitrary adelic point proves preservation of cuspidality by real Lie generators.

Induction on the enveloping algebra extends preservation to all enveloping operators. The constant-term covariance under right translation gives preservation by the finite and standard compact actions.

`cuspidalOperatorRealization` uses these three preservation laws to realize all cuspidal forms in the stable automorphic carrier. This internal construction uses the constant-term definition in Borel–Jacquet, *Automorphic forms and automorphic representations* (1979), §1.8 (1), printed p. 191, PDF p. 186, and proves the infinitesimal stability used for the cuspidal module in §2.2, printed p. 193, PDF p. 188.
