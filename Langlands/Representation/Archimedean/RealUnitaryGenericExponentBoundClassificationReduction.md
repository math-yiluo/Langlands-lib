# Deduction of the real exponent bound from classification and uniqueness

`realUnitaryGenericExponentBound_of_classification` proves the implication from the generic unitary classification on irreducible real standard modules and uniqueness of positive-weight standard parameters to the Library's exact real exponent-bound proposition. The conclusion retains the arbitrary carrier universe `uV`.

The canonical-model reduction transports the irreducibility, genericity and infinitesimal unitarity hypotheses to `realStandardModule n ds`. The classification premise then gives a second standard presentation by a list `es` satisfying `IsRealGenericUnitaryInducingData`. This is the input from Badulescu–Renard (2010), Theorems 8.1–8.2, p. 1131 (PDF p. 18), with Proposition 9.4, p. 1133 (PDF p. 20).

The normalization from the real pair-factor invariance reduction splits weight-zero blocks and replaces negative weights by positive weights. It preserves the actual standard function spaces and their ranks. The injective intertwiner from the classified list to the given list then gives an injective intertwiner of the normalized spaces. Their irreducibility follows from standard-module transport. Nontriviality and irreducibility make the normalized intertwiner surjective. The positive-weight uniqueness premise, derived from Knapp (1994), Theorem 1(c), p. 400 (PDF p. 410), identifies the normalized lists up to permutation.

Every block of the given list has at least one normalized block, and all its normalized blocks have its real exponent. The permutation associates such a block with the normalization of a block of `es`. The inducing-data exponent lemma gives the desired strict inequality.
