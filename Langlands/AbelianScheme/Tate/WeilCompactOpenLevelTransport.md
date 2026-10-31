# Canonical geometric-point comparisons of actual Weil level towers

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), Section III.1, printed p.91, describes levels as
monodromy-invariant orbits and states their canonical independence of the
geometric point. Printed p.92 gives the prime-to-p variant, and p.18
specifies rationalization of the integral Tate modules. The registered
source is `harris-taylor-2001-geometry-cohomology-simple-shimura`.
This module derives natural tower comparisons from the published actual
fixed-level path equivalences and the published geometric path-existence
theorem. The functor packaging and coherence proofs are internal deductions.

The abelian scheme `A/S`, its constructed dual, Poincaré evaluation and
named pullback-tensor, Picard pullback and finite Weil transition inputs
are those of `WeilCompactOpenLevels`. The base is quasi-separated. The
map called `polarizationMap` is an actual homomorphism into this dual;
this general interface imposes no polarization predicate. The rational
algebra action is `i : D →ₐ[ℚ] Rationalization.End A`, and the rational
source is a `D`-module `V` with form `ψ`. The coefficient ring is the
existing `FiniteAdeles ℚ`, or `PrimeToFiniteAdeles m` in the away version.
The same scalar comparison acts on the actual rationalized torsion
inverse limit and its actual section-ring Tate twist. No independent
pairing, monodromy action or twist trivialization is supplied.

Retain `TorsionFiniteEtaleStatement`, invertibility of the selected
positive torsion orders on `S`, and finite étaleness of their
root-of-unity group schemes. The full version selects all positive
orders. The away version selects orders coprime to a natural modulus
`m` and uses `PrimeToRationalProfiniteIntegerAdeleComparison h m`.
At a prime modulus this is the prime-to-that-prime version. Geometric
pairing compatibility is instantiated by the proved
`rationalWeilGeometricTransport`.

Write `T_s` for the compact-open tower at a field-valued point
`s : Spec Ω → S`, with finite fibres for its actual finite étale cover
fibre functor. The index category is respectively
`FiniteAdelicScalarExtensionLevel D V ψ` or
`PrimeToScalarExtensionLevel D V ψ m`. A tower object at `K` is the
set of right `K`-orbits of actual Weil-compatible frames fixed by the
actual finite étale fundamental group. It is the orbit that is fixed;
no fixed representative is required.

`weilAdelicCompactOpenLevelTransport p` constructs a natural isomorphism

`T_s ≅ T_t`

from a supplied path `p : fiberFunctor s hs ≅ fiberFunctor t ht`.
Its component at `K` is the existing actual equivalence
`weilAdelicLevelTransport ... K.toSubgroup p`, converted to an
isomorphism in the category of types. `NatIso.ofComponents` assembles
these components. Naturality is exactly the published
`weilAdelicLevelTransport_translate` equation for the transporter
arrow's element and subgroup condition. The `_hom_app` and `_inv_app`
lemmas identify both components definitionally with that equivalence
and its inverse.

The existing fixed-level path equivalence transports the actual Tate
module and twist together. Its path-independence theorem removes the
target monodromy loop relating two paths on the fixed orbit classes.
The theorem `weilAdelicCompactOpenLevelTransport_path_independent`
lifts this equality to the entire natural isomorphism using isomorphism
and component extensionality. Thus any two supplied paths with the same
endpoints produce equal natural isomorphisms, including their inverse
components.

The `_refl`, `_trans` and `_symm` lemmas prove identity, concatenation
and inversion of tower transport. Concatenation `p ≪≫ q` gives the
natural isomorphism `Transport p ≪≫ Transport q` in that order. Each
proof reduces by extensionality to the corresponding published
fixed-level equivalence law. The `_arrow` lemma states the elementwise
naturality square for every compact-open transporter arrow. Since this
includes inclusion arrows and, under their existing finite-dimensional
hypothesis, both Hecke arrows, transport is compatible with forgetting
and both Hecke legs.

For canonical comparisons additionally assume `[ConnectedSpace S]` and
`[IsLocallyNoetherian S]`. The endpoint fields are algebraically closed;
they can be different fields in universe `u`. The explicit finite-fibre
witnesses are retained. The published theorem `geometricPathExists`
then proves `Nonempty (fiberFunctor s hs ≅ fiberFunctor t ht)` for the
actual category of finite étale covers. Its proof assembles the actual
geometric Galois-category and fibre-functor theorems with the categorical
fibre-functor isomorphism theorem, as documented in
`GeometricPathProof.md`.

`weilAdelicCompactOpenLevelGeometricTransport` chooses such a path and
applies the preceding natural isomorphism. The theorem
`_GeometricTransport_eq_path` proves equality with transport along every
supplied path with the same endpoints. Consequently this comparison is
independent of the auxiliary path choice. Its `_refl`, `_trans` and
`_symm` theorems give identity, transitivity through a third geometric
point and inversion, with no path appearing in their statements.
The proofs rewrite by `_eq_path` and apply the preceding path laws;
transitivity uses the concatenation of two paths whose existence has
been proved.

The names beginning `weilPrimeToAdelicCompactOpenLevelTransport` and
`weilPrimeToAdelicCompactOpenLevelGeometricTransport` implement the
same constructions and proofs for the away tower, with all order and
scalar hypotheses restricted as above.

These are natural isomorphisms of the actual fixed-orbit towers for one
abelian scheme and its fixed dual-valued map and rational action. The
module supplies canonical geometric-point independence for those
towers. It does not construct the PEL moduli functor, a comparison
between different abelian schemes, nonempty frame spaces, or positivity
or nondegeneracy of an arbitrary dual-valued map. Those are separate
constructions or hypotheses.
