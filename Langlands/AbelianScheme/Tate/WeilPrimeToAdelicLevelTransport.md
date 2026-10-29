# Path transport and level maps for actual prime-to-modulus Weil frames

This module constructs actual prime-to-modulus Weil-compatible frame
transport, its induced path-independent equivalence on geometrically fixed
right orbit classes, and right Hecke and forgetful maps with their laws.
All constructions explicitly assume the named proposition
`Langlands.AbelianScheme.RationalWeilGeometricTransportStatement`.

The sources are Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), p.18 and III.1, pp.91–92 (PDF pp.26,99–100), and
Kottwitz, *Points on some Shimura varieties over finite fields* (1992),
Section 5, pp.390–391 (PDF pp.18–19). They are registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura` and
`kottwitz-1992-points-shimura-finite-fields`. Harris–Taylor p.18 specifies
rationalization of the away integral Tate module, p.91 gives independence
of the geometric point and the right Hecke maps, and p.92 gives the
prime-to-p frame condition. Kottwitz describes that condition using the
actual Tate twist, right similitudes, left monodromy and fixed orbit
classes. The formulation for arbitrary modulus and supplied paths here is
a derived specialization of the published Library constructions.

## Selected orders and actual modules

Fix a natural number `m` and select the positive torsion orders `n` with
`Nat.Coprime n m`. With `m` a prime this is the prime-to-that-prime system.
Write `R = Global.PrimeToFiniteAdeles m`. The explicit scalar comparison is
`hAway : PrimeToRationalProfiniteIntegerAdeleComparison h m`, coupled to
the full comparison `h`. The target is the actual `RationalAway` module
of the abelian scheme, rationalized over the integers, with its constructed
`D ⊗[ℚ] R` action. The value module is the actual section-ring away twist
`TateTwist.Divisibility.RationalAway Γ(Spec Ω, ⊤) m`, with its constructed
`R` action. Neither carrier is supplied as arbitrary module data.

The remaining inputs are an actual abelian scheme over a quasi-separated
base, its dual-scheme geometry, Poincaré evaluation and the named
pullback-tensor, Picard and finite Weil transition dependencies. The map
`polarizationMap` is an actual homomorphism to that constructed dual; no
polarization predicate is imposed by this general interface. The rational
source is a `D`-module `V` with rational bilinear form `ψ` and an algebra
map `i : D →ₐ[ℚ] Rationalization.End A`. Let
`G = ScalarExtensionSimilitudes D V R ψ`.

The endpoints are field-valued points `s : Spec Ω → S` and
`t : Spec Ω' → S`, with finite fibres for their actual finite étale fibre
functors. A path `p` is a supplied isomorphism of those functors. Retain
`TorsionFiniteEtaleStatement`, invertibility on `S` of the selected
orders, and finite étaleness of the selected root-of-unity schemes.
Invertibility of orders that are not coprime to `m` is not assumed.
Geometric points over connected locally noetherian bases are the intended
PEL application, but those additional hypotheses are not needed once the
path and displayed inputs are provided.

## Transport and its laws

`weilPrimeToAdelicFrameTransport p` is an equivalence of the existing
`WeilPrimeToAdelicFrame` spaces. It postcomposes a frame `η` with the actual
`primeToFiniteAdeleAlgebraTransport` along `p`. The value equivalence is
`TateTwist.Geometry.sectionPrimeToFiniteAdeleTransport`, which uses the
canonical section-to-point-field comparison and actual root transport.
The second clause of `RationalWeilGeometricTransportStatement`, specialized
to the coprime-order predicate, states simultaneous preservation of the
actual pulled-back Weil pairing. This is exactly the compatibility needed
by `FormIso.transport`.

Thus the underlying map is `η ↦ τ_A ∘ η`, and an existential twist
trivialization is composed with the actual twist map `τ_1` inside the
compatibility proof. No trivialization is retained and no roots or basis
are chosen. The application theorem identifies the map pointwise with
`rationalTransport` for the selected orders. The frame `refl`, `trans`
and `symm` laws follow by subtype and linear-equivalence extensionality
from the actual Tate transport laws or their defining inverse maps.

`weilPrimeToAdelicFrameTransport_right` proves commutation with right
source composition, by extensionality. The `monodromy` theorem proves
that transport intertwines actual geometric monodromy through
`pathConjugation p`, reducing pointwise to `rationalTransport_monodromy`.

`weilPrimeToAdelicLevelTransport U p` applies `InvariantOrbit.equiv` to
this frame equivalence and its two equivariance laws. It is an
equivalence of the existing `WeilPrimeToAdelicLevel U` types at the two
endpoints, for any subgroup `U` of `G`. These types consist of whole right
`U`-orbit classes fixed by geometric monodromy, without requiring a fixed
representative.

`weilPrimeToAdelicLevelTransport_path_independent` proves equality of
these equivalences for any two supplied paths with the same endpoints.
The actual `rationalTransport_change_path` formula identifies their frame
maps up to the target loop `p.symm ≪≫ q`. The generic
`InvariantOrbit.equiv_eq_of_left` removes this left action on the invariant
orbit classes. The level `refl`, `trans` and `symm` lemmas then express
identity, concatenation and inversion; their proofs use quotient induction
and the corresponding frame laws.

## Right Hecke maps and forgetting level

For `g : G` and subgroups `U,U'`,
`weilPrimeToAdelicLevelTranslate g hg` maps `[η]` to `[η ∘ g]` under the
explicit source-to-target condition

`∀ u ∈ U, g⁻¹ * u * g ∈ U'`.

This is `g⁻¹ U g ≤ U'`. It specializes `InvariantOrbit.translate` with the
actual commuting monodromy and right actions, so it is well defined and
preserves fixed orbit classes. `weilPrimeToAdelicLevelForget hU`, for
`hU : U ≤ U'`, is its `g = 1` specialization, from finer to coarser level.

The `Translate_one` and `Forget_refl` lemmas prove identity laws.
`weilPrimeToAdelicLevelTranslate_comp` proves that translating by `g`
and then `k` equals translating by `g*k`; the two subgroup conditions
compose in this right-action order. `weilPrimeToAdelicLevelForget_comp`
proves transitivity of forgetting. These proofs specialize the generic
invariant-orbit translation identity and composition laws.

`weilPrimeToAdelicLevelTransport_translate` proves that path transport
commutes with right translation using `InvariantOrbit.map_translate`
and the actual frame equivariance theorems. The `Transport_forget` lemma
is its identity-element specialization.

The module proves independence from the supplied path, not existence of
paths between arbitrary geometric points. It constructs no topology or
compact-openness result, nonempty frame, finite-dimensional faithful PEL
datum, involution compatibility, alternation or nondegeneracy theorem.
Those remain separate hypotheses or obligations for the PEL application.
It constructs no transport between different abelian schemes by rational
isogenies or scheme base change, nor an unpointed PEL moduli functor.
