# Integration over left cosets

Worker 31 implements integration infrastructure for the actual quotient
`H \ G`, whose points are the sets `H g`. The subgroup need not be normal.
`rightTranslate` is a homeomorphism induced by right multiplication on `G`;
the identity and composition formulas are proved on representatives.

For an actual right-invariant measure on `H`, `orbitAverage` is the Bochner
integral of `h ↦ f(h g)`. Right invariance proves independence of the
representative `g`. `quotientAverage` is its descended function. The proof also
establishes compatibility with right translation. The integral is Lean's total
Bochner integral; no integrability is inferred merely from this definition.

`IsCompatible` records the precise property required of an actual quotient
measure: nonzero, regular, invariant under right translation, and satisfying
the Weil formula on compactly supported continuous complex functions, with
integrability of their subgroup averages. `CompatibleMeasureExists` is a
proposition, not an assumed theorem or a construction of such a measure.
The canonical homeomorphism for the trivial subgroup yields an actual measure
`trivialQuotientMeasure`, its regularity, right invariance, and integral formula.
With a nonzero regular right-invariant ambient measure and unit Dirac measure
on the trivial subgroup, `trivialQuotientMeasure_isCompatible` proves every
field of the compatibility property. Compactly supported continuous functions
are integrable because the ambient regular measure is finite on compact sets.
`trivial_compatibleMeasureExists` proves existence in this case. The proof
does not require an ambient compactness or a quotient-measure existence axiom.
General quotient-measure existence and the nontrivial unipotent case remain
explicit obligations.

## Original source and conventions

Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, second edition,
2015, section 2.6, printed pages 60–63, especially (2.47), Proposition 2.50,
Theorem 2.51 and (2.52); retained original PDF pages 73–76.
Registered source `folland-2015-abstract-harmonic-analysis-second`,
SHA256 `c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
The original text was read, and PDF pages 75–76 were directly viewed.

Folland uses `G / H`, left translation and left Haar measure, with
`P f(g H) = ∫_H f(g h) dh`. Our left quotient and right action reverse these
conventions; the corresponding average is `∫_H f(h g) dh` and therefore
requires **right** invariance of the subgroup measure. A previously constructed
left Haar measure cannot be used here without proving the needed right
invariance. Folland's general existence theorem requires equality of the
ambient and subgroup modular functions on the subgroup. That theorem is not
proved by the present interfaces.

The trivial-subgroup construction is a derived specialization, proved by
transport along an explicit homeomorphism. In that case ambient Haar
pushforward is legitimate because the quotient map is a homeomorphism.
No analogous pushforward construction is asserted for a noncompact subgroup.

## Lean dependencies and scope

Only pinned Mathlib is imported, at commit
`5ed2965256430c3649e86755f9576b54eca72435` with Lean 4.34.0.
The implementation reuses `QuotientGroup.rightRel`, quotient homeomorphisms,
Bochner integration, right-invariant-measure change of variables, and transport
of regular measures along homeomorphisms. The quotient has its quotient
topology; its measurable structure is explicitly required to be Borel.
No additive character, Schwartz–Bruhat space or general Haar abstraction is
duplicated. This file supplies infrastructure for the JPSS branch and does not
construct local factors or assert analytic convergence.
