# Scalars of actual ambient intertwiner composites

This derived adapter connects the scalar extraction of
`RationalUnramifiedScalarContinuation` to the actual compact restriction
maps and normalized induced representations. It is motivated by
Waldspurger IV.3, printed p.285 / PDF p.51 of
`waldspurger-2003-plancherel` (SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
On the source's generic irreducibility locus, Schur makes the
opposite-intertwiner composite scalar. This module applies the published
smooth Schur theorem at a supplied irreducible induced parameter.

## Actual maps and the scalar equations

The ambient topological group is locally compact and nonarchimedean.
Two supplied closed semidirect parabolics `P0 = M U0` and `P1 = M U1`
share a Levi subgroup. Closedness of both radicals, continuity of the
Levi projections and the existing unimodular-modulus conditions are
explicit. A common compact open subgroup `K` supplies both decompositions
`G = P0 K = P1 K`. The unramified family is any supplied family of
continuous positive Levi norm characters. The inducing object is in the
canonical `SmoothRep` category, with arbitrary carrier universe.

`compactIntertwiningOperator_smul` proves scalar compatibility of the
published conjugation by actual compact restriction/extension equivalences.
The published identity and injectivity results then give
`compactIntertwiningOperator_scalar_iff`: a compact operator is `c * id`
exactly when its original ambient intertwiner is `c * id`.

For actual ambient intertwiners `J10` from the first normalized unramified
induction to the second and `J01` in the reverse direction,
`compactIntertwiningCompositionScalar` is the fixed coefficient
`ell((compact J01)(compact J10)(v))`. It is defined before assuming
irreducibility, scalarity, normalization of the pair or rationality.

`compactIntertwiningComposition_scalar_iff` uses the published composition
law for restriction/extension conjugation. The compact composite is
`c * id` exactly when `J01.comp J10` is that same scalar times the
ambient identity. No information about the original operators or their
scales is discarded by passage to the compact picture.

## Applying smooth Schur

The Schur results additionally require separability of the ambient group.
Its topological group structure is supplied by the existing
`NonarchimedeanGroup` instance. These supply the topological hypotheses
of the published `Langlands.Schur.separableSmooth_scalarEndomorphism`.
They are not asserted here for every rational-point realization.

At the parameter in question, assume that the actual first normalized
induced `SmoothRep` is irreducible. Its smoothness is already part of the
constructed induced object. Smooth Schur applied to `J01.comp J10`
provides a scalar endomorphism. The compact/ambient equivalence gives the
same scalar equation on the compact picture. If `ell(v) = 1`, normalized
coefficient extraction recovers that scalar, proving the original
ambient composite equals the displayed extracted coefficient times its
identity. Applying any other normalized pair recovers the same scalar,
so the choice-independence theorem proves independence of both extraction choices.

## Rational families of supplied intertwiners

`compactIntertwiningCompositionScalarFamily` applies the pointwise
construction to two parameter-dependent families of actual ambient
intertwiners on an arbitrary parameter subset `Omega`. It uses the same
fixed compact vector and functional throughout that subset.

The numerator theorem takes explicit rationality proofs for both compact
families. The published rational-composition theorem multiplies their
whole-operator denominators; scalar numerator extraction then applies to
that rational composite. This produces one regular numerator `a` and a
regular denominator `b` nonzero everywhere on `Omega`, satisfying
`b(chi) * scalar(chi) = a(chi)`. Rationality of the supplied families
is a mathematical premise of this result. Neither irreducibility,
separability nor normalization of the extraction pair is needed for
this numerator construction.

No irreducibility of tempered parabolic induction in general is assumed
or concluded. This is a pointwise result on a supplied irreducible
parameter. The intertwiners are actual maps between the canonical
normalized inductions, but they are supplied arguments: the module does
not prove they are the continued standard integrals. Their construction,
full convergence and rationality, existence of a nonempty generic
irreducibility locus, orbit descent, the global scalar `j`, its
parabolic/duality/Weyl identities and `mu` remain separate obligations.
These retained representation-theoretic premises are not permitted
structural assumptions for completing the main Plancherel program.
