# Chamber normalizers from pro-p Iwahori factors

This internal construction works over a nonarchimedean local field at an
arbitrary universe, with the actual rational-point topology. It assumes the
single-group KP axioms for the supplied datum.

For an apartment chamber and a generic cocharacter, suppose the two unipotent
factors in its Iwahori decomposition are pro-p. Both factors lie in the actual
positive subgroup by the largest-pro-p property of a chamber fixer. The
centralizer-zero factor lies in the chamber fixer, which normalizes the
positive subgroup. Moving the right unipotent factor across that centralizer
factor therefore writes every fixer element as a positive element times an
actual centralizer-zero point.

`chamberPositiveCentralizerFactors` chooses these two factors and retains their
literal multiplication identity in the original rational-point group.

Inside the zero subgroup, the centralizer factor lies in the actual torus
normalizer and the Iwahori subgroup. The Tits projection consequently sends it
to one. The split Tits-system normalizer lemma now identifies the normalizer of
the positive subgroup with the chamber fixer. Mapping from the zero subgroup
back into the rational-point group yields the requested intersection identity.

This is a derived group-theoretic argument using the supplied Iwahori and Tits
axioms. The pro-p property of the unipotent factors is an explicit hypothesis
here; this module does not claim to establish it or the full available-data
maximal-pro-p statement.
