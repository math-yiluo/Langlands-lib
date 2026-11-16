# Lattice reduction for the actual polarized automorphism group

This internal adapter combines the actual Rosati norm identities with finiteness
of bounded sets in a finite free integral lattice. It is a conditional reduction,
and does not prove the final finiteness target without its displayed premises.
It introduces no replacement positive form or abstract automorphism group.

`polarizedAutTraceBallEmbedding` maps an element of the existing actual integral
polarized automorphism group to its underlying integral endomorphism. The norm
identity puts it in the sublevel set of `integralTraceForm` at the geometric trace
of the identity. Isomorphism and subgroup extensionality prove injectivity.
The embedding assumes the existing tensor and Picard prerequisites, per-object
dual data and additivity, and rational invertibility of the given map. It needs
no positivity or finite-freeness assumption.

`finite_polarizedAutGroup_of_traceForm` additionally assumes characteristic zero,
that the actual integral endomorphism module is finite and free over the integers,
and symmetry and strict positivity of the actual rational Rosati trace form.
Characteristic-zero injectivity of `homToHom0` transfers strict positivity to
nonzero integral endomorphisms. `Langlands.finite_rational_bilinear_le` then gives a
finite sublevel set, and the embedding gives finiteness of the actual group.
This uses the algebraic bounded-lattice theorem; no real compactness or
dimension formula for the trace is used.

`polarizedAutomorphismFiniteness_of_rosati_and_lattice` returns exactly the
existing `PolarizedAutomorphismFinitenessStatement`, conditional on three explicit
mathematical premises: the existing actual `Rosati.RationalInverseStatement`,
the existing actual `Rosati.PositivityStatement`, and finite freeness of the
actual integral endomorphisms over every algebraically closed
characteristic-zero field in the target universe. It packages the target's
existing geometric witnesses as `Rosati.Prerequisites` and `Rosati.DualData`,
uses the published field dual-map additivity theorem, obtains rational
invertibility and positivity from the corresponding premises, and applies
the pointwise lattice reduction. The three premises are proof obligations for
the final target and are not discharged by this module.
