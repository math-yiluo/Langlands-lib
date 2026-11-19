# Affine analytification detects quasi-finiteness

`Langlands.Analytic.AffineAnalytification.affineAnalytificationQuasiFinite`
proves `AffineAnalytificationQuasiFiniteStatement` in the three independent
universes of the field and the two algebras. The target specializes
Corollary 3.1.7 of Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), printed p. 56, to the affine polynomial-locus analytification
over \(K\). The registered source is `berkovich-1993-etale-cohomology`
(PDF p. 53).

For a quasi-finite algebraic map, the seminorm kernel at a source point
is prime. Zariski's Main Theorem gives a finite algebraic factor followed
by a map that becomes an isomorphism after inverting an element outside
that prime. The intermediate algebra is of finite type over \(K\), so
the proof chooses a finite polynomial presentation for it. For the
finite factor, a sufficiently large target chart contains the image
point in its interior. The full inverse image of that chart is a
saturated source chart with a finite Banach pullback. Its interior
contains the inverse image of the target chart interior. Finiteness on
the two charts gives finiteness at the intermediate analytic point.
The principal-open transport lemma then transfers finiteness to the
composite at the original source point.

For the reverse implication, finiteness at each point gives a finite fibre
in an open neighborhood. The other points of that fibre form a finite
closed set, which can be removed to isolate the original point. The
fibre-isolation converse uses a compact chart containing infinitely many
points of one fibre whenever the algebraic map fails to be quasi-finite.
