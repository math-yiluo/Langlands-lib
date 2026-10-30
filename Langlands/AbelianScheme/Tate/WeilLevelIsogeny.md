# Rational-isogeny transport of actual Weil-compatible level orbits

Worker 142. This derived unit applies the actual full and away compatible-frame
isogeny equivalences of `WeilFrameIsogeny` to the geometrically fixed right-orbit
sets `WeilAdelicLevel` and `WeilPrimeToAdelicLevel`. The source and target are
actual abelian schemes over the same quasi-separated base, with constructed
duals, specified integral dual-valued maps and rational algebra actions. The
rational isogeny intertwines these actions and satisfies the actual Hom0
equation `e^vee lamB e = q lamA` for a rational unit `q`. The dual-valued maps
are not asserted to be polarizations. No pairing equation or arbitrary
monodromy representation is substituted for these geometric inputs.

The frame monodromy laws are proved by subtype and linear-equivalence
extensionality, reducing to the existing equivariance of the actual rational
Tate map of an isogeny. They retain both the actual geometric fundamental
group of the finite-etale fibre functor and the actual twist monodromy in the
compatible-frame action. Together with the previously proved right-action
law, this gives a biequivariant equivalence. `InvariantOrbit.equiv` then
constructs an equivalence on the monodromy-fixed orbit sets. Thus the orbit
class is fixed; no representative is required to be fixed.

The Hecke compatibility laws use `InvariantOrbit.map_translate`. With source
subgroup `U`, target subgroup `U'` and right translation by `g`, the condition
is `g^-1 U g` contained in `U'`. Specializing to the identity source
similitude proves compatibility with forgetting a finer subgroup level.
The frame path squares reduce to the existing naturality of rational Tate
transport for an isogeny. Quotient induction then proves the path squares
on fixed level orbits. The existing path maps are independent of the chosen
path on fixed orbits, so these squares apply to every such path without
introducing an additional choice.

All original tensor/Picard coherence, dual geometry, Poincare inverse
evaluation and finite Weil transition inputs remain explicit. The named
`RationalWeilFunctorialityStatement` supplies the geometric-multiplier
restriction to compatible frames, and the named
`RationalWeilGeometricTransportStatement` supplies their geometric actions
and paths. Finite-etaleness of torsion is a named explicit theorem input;
selected orders are units on the base, and the corresponding roots-of-unity
schemes are finite and etale. Finite geometric fibres of all covers are
specified at each point. The full version selects all positive integers;
the away version selects those coprime to an arbitrary natural modulus,
including the prime-to-p case. Its modules and actual twist use the same
coupled scalar comparison. There is no assertion of frame nonemptiness,
polarization nondegeneracy, compact-open topology, or identity/composition
of geometric multiplier equations in this unit.

The provenance is the specialization of the existing geometric Tate,
twist, compatible-frame and invariant-orbit constructors to the actual
rational-isogeny map. Harris--Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), printed p.18 and Section III.1,
pp.90--92, gives the rational-isogeny convention, invariant-orbit levels,
right Hecke action, and prime-to-p version. Kottwitz, *Points on some
Shimura varieties over finite fields* (1992), Section 5, pp.390--391,
explains the same fixed-orbit condition, commuting actions and retained
Tate twist. The proof here uses the already constructed Library maps and
quotient helpers; these source passages are the intended moduli
interpretation, rather than literal proofs of this relative Lean
specialization. No source-specific errata note was found in the consulted
project notes.
