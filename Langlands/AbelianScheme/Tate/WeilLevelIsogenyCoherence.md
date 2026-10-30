# Coherence of actual Weil-compatible fixed-level isogenies

Worker 142. This derived unit constructs direct composite and inverse
rational-isogeny transport on `WeilAdelicLevel` and
`WeilPrimeToAdelicLevel`, and proves their identity, composition and inverse
laws. These are the existing sets of geometrically fixed right-orbit
classes of actual Weil-compatible Tate frames. The subgroups may be arbitrary;
the statements therefore apply in particular to compact open levels once the
appropriate topology is supplied.

All endpoints are actual abelian schemes over the same quasi-separated base.
Their constructed duals, dual geometry, inverse Poincare evaluations,
integral dual-valued maps and rational algebra actions remain explicit. For
rational isogenies `e : A -> B` and `f : B -> C`, the hypotheses are the
intertwining equations for those algebra actions and the actual rational dual
pullback equations `e^vee lamB e = q lamA` and
`f^vee lamC f = r lamB`, with rational units `q,r`. The intermediate
abelian scheme and its data are shared. Additivity of the constructed dual
map is explicit for each ordered pair used in the pullback calculation.

`weilAdelicLevelIsogenyComp` and its prime-to counterpart apply the published
single-isogeny level equivalence to `e.trans f` with multiplier `q*r`.
`IsRationalDualPullbackMultiple.comp` derives its geometric multiplier equation,
and `rationalIntertwines_comp` derives its algebra-intertwining equation.
The direct equivalence equals successive transport, first by `e` and then
by `f`. The identity laws use the actual identity rational isogeny, the
derived unit multiplier equation and its algebra-intertwining law.

The inverse definitions apply single-isogeny transport to `e.symm` with
multiplier `q^-1`. Their reverse geometric multiplier and intertwining
equations are derived by `IsRationalDualPullbackMultiple.inv` and
`rationalIntertwines_inverse`. The inverse laws identify these direct maps
with the inverse equivalences of forward transport. No additional pairing
preservation hypothesis for the identity, composite or inverse is assumed.

For all six coherence proofs, extensionality first reduces an equality of
equivalences to the equality of the underlying orbit classes. The proof then
unfolds `InvariantOrbit.equiv` and its map on quotient classes. Quotient
induction reduces the goal to equality on a frame representative; applying
`RightOrbit.mk` to the corresponding published compatible-frame coherence
law proves it. This induction makes no assertion that any representative is
geometrically fixed: only its orbit class is fixed. The commuting geometric
and right actions used in the quotient remain the existing actual actions.

The named finite Weil transition, rational Weil functoriality and rational
Weil geometric transport statements remain explicit inputs. Torsion
finite-etaleness is a named theorem input; selected orders are units on the
base, and the corresponding roots-of-unity schemes are finite and etale.
Finite geometric fibres of finite-etale covers are specified at the chosen
field-valued point. The full version selects all positive integers; the away
version selects those coprime to an arbitrary natural modulus. Each version
uses the same scalar comparison for its modules and actual twist, with the
away comparison coupled to the full one. No roots of unity or trivialization
of twist monodromy are chosen. This unit does not assert that the dual-valued
maps are polarizations, that frames exist, that the forms are nondegenerate,
or that a compact-open topology or pointed-base-change functor has been
constructed.

The provenance is quotient descent of the published actual compatible-frame
coherence laws through the published fixed-orbit equivalences. Harris--Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001),
printed p.18 and Section III.1, pp.90--92, provides the rational-isogeny
convention and the motivating invariant-orbit level structures and isogeny
relation, including the prime-to-p variant. The present coherence laws are
derived Library consequences; that passage is not cited as a proof of
additional geometric existence results. No source-specific errata note was
found in the consulted project notes.
