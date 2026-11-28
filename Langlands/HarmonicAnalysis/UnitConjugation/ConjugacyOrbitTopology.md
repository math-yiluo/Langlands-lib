# Conjugacy orbits in finite-dimensional topological algebras

Let `A` be a finite-dimensional algebra over a \(T_1\) topological field `F`.
The topology on `A` is its module topology and makes it a topological ring.
`ConjugationOrbitTopologyStatement` says that for each `N : A`, the orbit
`conjugationSaturation {N}` is locally closed in `A` and is homeomorphic to the
space of left cosets of `conjugationCentralizer N` via \(Cg\mapsto g^{-1}Ng\).
The universes of `F` and `A` are independent.
`isLocallyClosed_conjugationOrbit` gives the first assertion.
`conjugationOrbitHomeomorph` constructs the homeomorphism, and
`conjugationOrbitHomeomorph_mk` gives its value on a coset representative.
`conjugationOrbitTopology` packages these results.

For the rank argument, fix `N` and let \(T_X(z)=Xz-zN\). At a reference point
`X₀`, choose a linear section \(i:\operatorname{im}T_{X_0}\to A\) of \(T_{X_0}\)
onto its image and a projection \(p:A\to\operatorname{im}T_{X_0}\). The matrix of
\(pT_Xi\) is continuous in \(X\) and equals the identity at \(X_0\). Its
determinant is therefore nonzero near \(X_0\). This gives lower semicontinuity of
\(\operatorname{rank}T_X\). Within this neighborhood, when the rank equals
\(\operatorname{rank}T_{X_0}\), the restriction of \(p\) to \(\operatorname{im}T_X\)
is both surjective and injective. For \(z_0\in\ker T_{X_0}\), the correction
\[
z(X)=z_0-i(pT_Xi)^{-1}pT_Xz_0
\]
is continuous at \(X_0\), has value \(z_0\) there, and is in \(\ker T_X\) on the
nearby equal-rank locus.

Left multiplication by a conjugating unit shows that the rank is constant on
the orbit of `N`. Lower semicontinuity bounds the rank above by that constant
on the closure of the orbit. Thus near an orbit point \(X_0=uNu^{-1}\), the
rank on the closure is constant. Apply the correction to \(z_0=u\). The
open unit embedding ensures that \(z(X)\) belongs to the image of any
specified neighborhood of \(u\) in \(A^\times\) for \(X\) sufficiently close
to \(X_0\). The equality \(T_X(z(X))=0\) then expresses \(X\) as a conjugate by
a unit in that neighborhood. This proves that the orbit is open in its
closure and that the map \(u\mapsto uNu^{-1}\) is open onto the orbit.

The continuous open map \(g\mapsto g^{-1}Ng\) descends along the left quotient
projection. Equality of two images is equivalent to equality of their left
cosets, so the descended map is bijective. The quotient topology gives both
continuity and openness of this bijection.

The local-field application is the orbit model used by
`OrbitalDistribution`. Harish-Chandra, *Admissible invariant distributions on
reductive p-adic groups* (1999), §3.1, printed pp. 17–18 (PDF pp. 32–33),
uses the homogeneous space \(G/C_G(N)\) to integrate along the orbit. The
opening of §3.2, printed p. 19 (PDF p. 34), describes local closedness for
nilpotent orbits by their dimension strata. Inversion converts the source's
right cosets to the left cosets used here.

Source `harish-chandra-1999-admissible-invariant-distributions`,
SHA-256 `d68d7fde0036e7236eaf84d356b1d793bd15b0109d1aaf5787ca4bf47fe6bb19`.
