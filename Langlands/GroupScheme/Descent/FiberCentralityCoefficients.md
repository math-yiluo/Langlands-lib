# Finite coefficients preserving affine residue-fibre centrality

This internal derived module extends the supplied Hopf-map coefficient
construction to actual homomorphisms of affine group schemes over a commutative
ring `R`, in any common universe. The fibres use the canonical scheme residue
fields and full scheme pullbacks. Centrality is the all-test-scheme predicate.

`centralFiberLocus i` consists of the primes where the canonical residue-field
pullback of `i` is central. A commuting square with source and target group
isomorphisms identifies these loci by applying the pullback functor to the
square. For affine groups, `AffineHopfMorphism.pullback` and the actual
`AffineCoordinates.hopfSpecIso` identify this locus with the canonical
Hopf-map centrality locus.

`centralFiberLocus_baseChange` identifies the locus of the actual scalar
extension to any commutative `R`-algebra `S` with the inverse image of the
original locus under prime contraction. The proof first transports the
coordinate isomorphisms through pullback, then uses the natural scalar-extension
Hopf-spectrum isomorphisms and the Hopf locus inverse-image identity.
There is no finite-type or noetherian hypothesis for this identity.

If `R` is noetherian, both groups are affine, and their structure morphisms
are locally of finite type, their actual coordinate Hopf algebras are finite
type. The Hopf constructibility theorem then proves that `centralFiberLocus i`
is constructible.

Under these hypotheses, let `S` be any commutative `R`-algebra and assume
`h` says that the centrality locus of the actual scalar extension of `i` to
`S` equals the whole spectrum. Thus every canonical residue-field fibre of
that scalar extension is central.
`exists_fg_subalgebra_centralFibres S i h t` produces a finitely generated
`R`-subalgebra of `S` containing the prescribed finite set `t` on which this
supplied fibrewise centrality still holds.
`centralFiberCoefficientModel S i h t` retains the coefficient subalgebra,
finite generation, containment of `t`, its noetherian property, and centrality
of every canonical residue fibre of the actual pulled-back homomorphism.
No noetherian assumption on `S` is required.

The coefficient proof applies constructible fullness detection to the actual
directed spectrum limit of finitely generated subalgebras. The noetherian
property follows from finite generation over `R`. This module constructs
neither reductive models nor global centrality; the host central-isogeny
criterion still requires those steps.
