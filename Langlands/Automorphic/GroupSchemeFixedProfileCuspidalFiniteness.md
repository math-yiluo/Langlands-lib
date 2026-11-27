# Cuspidal finiteness for fixed level, central ideal and compact profiles

`FixedProfileCuspidalFinitenessStatement` concerns submodules of the finite
plot-smooth rational functions of an affine connected reductive group over a
number field, using the supplied archimedean smooth realization and its
differential action. The positive-rank closed matrix representation supplies
the norm for moderate growth and the height whose sublevels are compact.
Each function is cuspidal, has moderate growth, is fixed by one common open
finite level, and is killed by one cofinite ideal of the actual enveloping
center. On every finite slice its right profiles belong to one fixed
finite-dimensional space on the supplied archimedean maximal compact subgroup.

The proof chooses the central derivatives associated to a lifted basis of
the finite center quotient. The elliptic interior estimate first bounds all
derivatives of each individual function using its moderate growth exponent.
Differentiation commutes with the proper constant terms and preserves finite
level. Apply `adelicNormOneCuspidalFamilyRapidDecay` at order zero to the
selected derivatives of an individual function. Rational invariance extends
the bound on the chosen representatives to the whole norm-one subgroup.
Use the resulting finite norm-one supremum of the derivatives as the size
of the function. The central quotient and interior estimates give uniform
polynomial growth for the derivative family with this size factor. Apply the
same decay theorem at order one to that family to bound the derivatives by
half the size on norm-one representatives outside a common compact height
sublevel.

Within the compact sublevel, the invariant first derivative bounds give oscillation by
half the size on small archimedean neighborhoods. Open finite level gives constant
values in the finite directions. A finite cover of the compact sublevel therefore gives
finitely many evaluations of the selected central derivatives. If these evaluations
all vanish, the value bounds on the compact set and its exterior force the norm-one
supremum to be zero. The central quotient estimate then forces the original function
to vanish. The linear map of these evaluations is injective with finite-dimensional
codomain.

This is a boundedness proof of the cuspidal step of Harish-Chandra, *Automorphic Forms
on Semisimple Lie Groups* (1968), I §6, Lemma 18, using the positive central factor
in Borel–Jacquet, *Automorphic forms and automorphic representations* (1979), §1.6(1),
and the adelic statement in §4.3 (i).

Both decay applications use `AdelicNormOneCuspidalFamilyRapidDecay`, the
specialization to the full parabolic index of Bernstein–Lapid, *On the
meromorphic continuation of Eisenstein series* (2024), §7.4, printed
pp. 216–217 (PDF pp. 30–31).
