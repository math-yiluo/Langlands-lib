# Harish-Chandra finiteness on the rational adelic quotient

The proof of `rationalHarishChandraFiniteness_of_leviCenterRestriction` uses
strong induction on the dimension of the actual Lie kernel. It assumes finite
restriction of the infinitesimal equations via
`ParabolicLeviCenterRestrictionStatement`.

For an affine connected reductive group over a number field, fix an open
finite level, a maximal compact subgroup of the infinite point group, a
cofinite ideal of the actual archimedean enveloping center, and a
finite-dimensional space of right profiles on the compact subgroup.
For a positive-size closed matrix representation, impose these conditions
on the submodule of finite plot-smooth rational functions of moderate
growth in its matrix height. The center ideal acts on every finite slice
using the supplied smooth realization and differential action. A size-zero
closed matrix representation has trivial adelic points, which already
gives finite dimension.

Take the product of the normalized integrals along the unipotent radicals of
the proper standard parabolics. Each image is finite-dimensional. The fixed
profile transfer gives the necessary conditions on the parabolic quotient.
For each constant term, evaluating the profiles against elements of the
dual of the profile space gives a linear map whose range contains all of its
right compact translates. This proves compact finiteness on the parabolic
quotient with the same profile bound.
Iwasawa uses the prescribed archimedean maximal compact, and restriction to
finitely many translates of the actual Levi detects the parabolic image. The
Levi is a proper smooth closed subgroup, so the dimension induction applies
there. The set of simple relative roots is finite, so the product of these
images has finite dimension. The kernel consists of cuspidal functions by
rational conjugacy of parabolics. The cuspidal estimate applies to its image
in the original smooth carrier. The finite-dimensional kernel and quotient
give finite dimension of the whole submodule. Its image under evaluation
contains the generators of the desired span of adelic functions.

The proof adapts Harish-Chandra's argument with proper constant terms and
their cuspidal kernel in *Automorphic Forms on Semisimple Lie Groups* (1968),
I §2, Theorem 1, and I §6, printed pp. 8 and 17–20 (PDF pp. 18 and 27–30).
Harish-Chandra inducts on rational rank for the real arithmetic quotient.
The adelic proof above inducts on Lie dimension. Borel–Jacquet, *Automorphic
forms and automorphic representations* (1979), §4.3(i), printed p. 195
(PDF p. 190), gives the
reductive fixed-data adelic finiteness result. Mœglin–Waldspurger,
*Spectral Decomposition and Eisenstein Series* (1995), I.2.17,
printed pp. 37–38 (PDF pp. 20–21), explains the passage to finitely many
translated restrictions on the Levi together with the finite homomorphism
of centers. The restriction in the proof is unnormalized and uses the
finite homomorphism in that convention.
