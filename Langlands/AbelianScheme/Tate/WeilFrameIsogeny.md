# Rational-isogeny transport of actual Weil-compatible frames

Worker 142. This derived construction restricts the published actual Tate-frame
isogeny transport to the existing `WeilAdelicFrame` and
`WeilPrimeToAdelicFrame` spaces. Fix abelian schemes `A` and `B` over a
quasi-separated base, their constructed duals, integral dual-valued maps `lamA`
and `lamB`, and rational algebra actions `iA` and `iB`. An invertible rational
homomorphism `e` must intertwine these actions and satisfy the geometric equation
`e^vee lamB e = q lamA` in the actual rational Hom group, for `q : Q^units`.
The maps need not be polarizations for the construction; polarized applications
can supply that additional property.

The helper lemma derives the rational pairing multiplier formula for the
existing integral-map pullbacks from the Hom0 formula of `WeilHom0Pullback` and
its integral-inclusion identities. This retains the named
`RationalWeilFunctorialityStatement` as an explicit theorem dependency. No
pairing-preservation equation or arbitrary target equivalence is supplied as
replacement data.

Both equivalences send a compatible frame `eta` to `V(e) composed with eta`.
They use the existing tensor-algebra-linear `finiteAdeleAlgebraIso` and
`primeToFiniteAdeleAlgebraIso`. On the value module the equivalence is
multiplication by the diagonal image of the rational unit `q`, on the actual
rational Tate twist over the geometric test scheme. The proved diagonal scalar
action identities identify this operation with rational multiplication. The
geometrically derived pairing multiplier then permits `FormIso.transport`.
Consequently the existential twist trivialization of a frame is composed with
this twist automorphism; no basis, roots of unity or chosen trivialization is
introduced. Both inverse maps exist because `e` and `q` are invertible.

The application laws identify the underlying function with the actual
`rationalHomMap`. The underlying-frame laws identify the maps with the existing
ambient adelic and away frame transport, and the right-action laws prove that
source precomposition commutes with this transport. The away version uses the
same coupled scalar comparison `hAway` for the module and the twist and works
for any natural modulus, including the prime-to-p case. All dual geometry,
Poincare inverse evaluation, tensor/Picard coherence, finite transition,
dual-map additivity and rational functoriality inputs remain explicit.

The provenance is a specialization of the published rational Hom, dual map,
actual Tate, Weil and compatible-frame constructors. Harris--Taylor, *The
Geometry and Cohomology of Some Simple Shimura Varieties* (2001), printed p.18
and Section III.1, pp.90--91, uses invertible rational homomorphisms and their
postcomposition on level frames. The pairing convention and geometric
compatibility originate in Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft built 2012-02-08, Chapter XI Definition (11.11),
printed p.162 / PDF p.166, Proposition (11.21)(i), printed p.167 / PDF p.171,
and paragraph (11.23), printed p.168 / PDF p.172. Their field-level finite
identity and inverse-limit twist motivate the explicit rational theorem
dependency; this unit does not prove it or attribute its full relative scope
literally to those passages. No source-specific errata note was found in the
consulted project notes.

This unit does not construct monodromy-fixed level transport, prove
composition of geometric multiplier equations, assert frame nonemptiness or
establish PEL nondegeneracy or compact-open topology.
