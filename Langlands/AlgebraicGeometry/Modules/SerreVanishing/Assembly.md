# Assembly of two-bundle Serre vanishing from section killing

The internal theorem `properAmplePairSerreVanishing_of_sectionKilling` reduces the
exact published `ProperAmplePairSerreVanishingStatement` to the explicit
`SerreVanishing.SectionKillingStatement` premise. It retains the arbitrary
universe, all proper schemes over all fields, all coherent coefficients, and all
pairs of ample line bundles.

Properness makes the scheme quasi-compact, locally noetherian, and separated.
The Dimension module gives a natural bound `d` on its topological Krull dimension,
which bounds the support of every coefficient by `d + 1`. The Devissage theorem
then supplies `Good` with this support bound. Unfolding that predicate gives
exactly the target's one threshold for both exponents and every positive degree.

This is a derived internal assembly lemma. Its section-killing premise is
explicit, and an unconditional proof must supply that premise before this
assembly proves the published target.
