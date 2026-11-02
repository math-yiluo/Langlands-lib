# Functoriality and compact subgroups of actual norm-one adelic points

This internal construction uses the actual group-scheme point groups and the normalized character norms of `AdelicGroupNormOne`. It proves that group-scheme morphisms induce continuous homomorphisms on the full adelic groups and on their norm-one subgroups, and that these maps commute with principal rational points.

For every rational character of the target group, evaluation after the point map is evaluation of the character pulled back to the source group. Applying the actual normalized idele norm proves that the image of the source norm-one subgroup lies in the target norm-one subgroup. No surjectivity assertion is made.

Every compact subgroup of actual adelic points lies in the actual norm-one subgroup. The implemented proof establishes a general elementary lemma: a continuous homomorphism into the positive real units is trivial on a compact subgroup. The nonnegative real value attains its maximum; evaluating at the square of a maximizing group element forces that maximum to be at most one. Applying the same bound to inverses gives equality with one. Applying this lemma to every actual character norm proves the inclusion.

The construction is derived from the character-kernel definition in Getz–Hahn, *An Introduction to Automorphic Representations*, §2.6, equation (2.19), printed pp.67–68. The compactness argument is internal and elementary. This module supplies no choice or existence of maximal compact subgroups, minimal parabolics, reduction domains, finite-volume assertions, or analytic modular-character comparisons.
