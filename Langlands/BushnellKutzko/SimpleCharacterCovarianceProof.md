# Covariance from centralizer intertwining

`simpleCharacter_cutoffJ_conjugationRatio` uses invariance under J and the adjoint-image inclusion in the trace dual to show that a cutoff J unit has trivial trace error. The dual is stable under multiplication by the cutoff lattice, so the statement applies to the full conjugation difference.

`simpleCharacter_covariance_of_centralizer_intertwining` factors the outer group into a mixed group and cutoff J. The mixed and J calculation gives the trace ratio for the mixed group, and composition with cutoff J and the centralizer gives the ratio on the double coset. The auxiliary depth is supplied independently, as in `SimpleCharacterCovarianceStatement`. The calculation is the one in BK93 (3.3.5) and (3.3.9), printed pp. 107–108.
