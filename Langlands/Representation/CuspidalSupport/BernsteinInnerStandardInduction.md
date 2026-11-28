# Normalized induction through a represented standard Levi

Let \(M\to G\) be a closed representative of the standard Levi with label
\(J\) in a Bernstein family for \(G\). The base field is a nonarchimedean
local field. The rational point groups of \(G\) and \(M\) have the canonical
point topologies and carry the local compactness and nonarchimedean group
instances in `BernsteinInnerStandardInductionStatement`. The representation
carriers have universe `max u v`, where `u` is the field universe.

`BernsteinLeviPresentation.standardFamily` factors the ambient maximal split
torus through \(M\). It uses `standardLeviStandardFamilies` to retain the same
generic cocharacter. The simple roots of \(M\) identify with the roots in
\(J\). For an intrinsic label \(K\), `innerIndex` gives the corresponding
subset of \(J\), and `leviIndex` interprets it as an ambient label \(L\).
`innerSubgroups` identifies the intrinsic parabolic, Levi and unipotent
subgroup functors with the preimages of the ambient ones for \(L\).
`innerLeviIso` identifies the two inducing Levi schemes by uniqueness of
representatives. Its composite with the ambient Levi inclusion is the
intrinsic Levi inclusion followed by \(M\to G\).

`innerInductionStagesIso` transports the intrinsic normalized induction along
the multiplicative homeomorphism from \(M(F)\) to its literal image in
\(G(F)\). The three preimage equalities give the membership equivalences for
`GroupTransport.inductionIsoApp`. On the inducing Levi points the inclusion
identity for `innerLeviIso` gives equality of the two actions on the original
carrier. The comparison cancels inverse pullbacks with
`SmoothRep.pullbackSymmIso`. Applying outer induction and the component of
`bernsteinStandardInductionStagesIso` then gives direct normalized induction
in \(G\) from the transported representation at \(L\).
`bernsteinInnerStandardInduction` witnesses the resulting isomorphism for
every smooth inducing object.

The comparison is derived from the description of parabolics inside a Levi
in Renard, *Représentations des groupes réductifs p-adiques*, French edition of
9 July 2026, V.3.10–V.3.11 (printed p. 112, PDF p. 118) and from transitivity
of normalized induction in VI.1.4 (printed pp. 136–137, PDF pp. 142–143).
