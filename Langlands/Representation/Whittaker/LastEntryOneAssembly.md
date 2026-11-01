# Coordinates and scalar assembly for the last-entry-one expansion

Author: Worker 186.

This module supplies the coordinate and scalar-functional helpers used by
`LastEntryOneAsymptoticProof`. Its general `assemble` theorem takes a
root-coordinate expansion as input. The final proof supplies that expansion
from the published `Whittaker.jpsDecomposition` theorem after establishing its
hypotheses through `LastEntryOneAdapters` and `LastEntryOneGerms`.

The coordinate definitions repeat the exact diagonal and simple-root
conventions in Worker 394's published statement. `rootLift` extends an
`n`-tuple by the last coordinate one and takes cumulative products. Its
two inverse identities and last-entry formula specialize the published
`RankinSelberg.rootCoordinateChange` theorem; no Haar-measure conclusion is
needed here. All ranks include `n = 0`.

The finite-function pullback uses the published
`RankinSelberg.finiteFunctionClosure`. Its multiplication convention is
`f (b * a)`, exactly as in the target. The root homomorphism is continuous.
Since it has the explicit section `rootLift`, pullback of complex functions
is injective; a finite set of functions therefore incurs no collisions.

The conditional theorem `assemble` assumes a uniform root-coordinate expansion
for one functional and scalar spanning of all eligible functionals by that
functional. It chooses the image of the root finite set under pullback. For a
functional equal to `c` times the fixed one, it multiplies every Schwartz–Bruhat
coefficient by `c`. The inverse coordinate identity gives the equation for
every diagonal whose last entry is one; injectivity permits `Finset.sum_image`
without grouping repeated functions. The finite set is chosen before the
functional and vector. The scalar-spanning and root expansion assumptions
remain explicit hypotheses.

The helper `mem_glFunctionals_of_raw` converts the target's conjunction of
entrywise unipotence conditions into the published bundled Whittaker-functional
predicate. It uses `UnitaryAdditiveCharacter.ofComplex`, so it explicitly
requires the raw character to be continuous, nontrivial, and of unit norm.
The entrywise equivalence has the same product of simple upper entries as
the target.

These are internal assembly facts for the derived full-torus packaging
explained in `LastEntryOneAsymptoticStatement.md`. The underlying source
is JPS (1979), Proposition 2.2 and Lemma 2.2.1, printed pages 181–183
(registered source `jps-1979-gl3-i`). The helpers are derived algebraic and
topological arguments for that packaging; the function-space expansion is
supplied in the final proof module.
