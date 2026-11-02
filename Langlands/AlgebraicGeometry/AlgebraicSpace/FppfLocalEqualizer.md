# Immersed equalizer loci from fppf-local representatives

Author: Worker 509.

This internal construction applies to every type-valued fppf sheaf on all schemes
over an arbitrary base scheme `S`, in universe `u`. For any test scheme `T` and
any two sections `x, y`, `sectionEqualizerSieve` is the sieve on `T.left` of
morphisms along which those sections agree. It is obtained from the ordinary
presheaf equalizer sieve by the slice-sieve equivalence. Sheaf separatedness
makes this sieve closed for the fppf topology. This topology-theoretic closedness
does not assert that a locus is a closed subscheme.

The factorization lemma translates the published `RepresentsEqualizer`
criterion over `S` into the identical criterion on underlying scheme morphisms.
The structure map on a prospective lift is forced by its composite with the
representing immersion.

If a covering sieve of `T` has immersed representations for the restrictions
of `x` and `y` on each member, the published `fppfImmersionLocusDescent` glues
these representations. The proof transfers the covering sieve to the underlying
scheme, uses functoriality to identify the pulled-back equalizer sieve, applies
descent, and equips the resulting scheme with its composite map to `S`.
It returns `RepresentsEqualizer` and an actual immersion. There is no restriction
to sections with global representatives, or to reduced, affine or quasi-compact
tests. No immersion-existence assertion without the local hypotheses is made.

The provenance is an internal application of the published descent theorem,
the slice-sieve equivalence and fppf sheaf separatedness. No external literature
is newly used. In particular, this construction supplies the passage from local
representatives to all sections, while the geometric existence of the local
immersions remains a separate input.
