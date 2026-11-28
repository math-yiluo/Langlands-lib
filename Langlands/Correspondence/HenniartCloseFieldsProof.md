# Close-fields orbit counts from the filtered Galois quotients

## Result

`Langlands.Henniart.closeFieldsTwistCountFromGaloisQuotient` proves
`Langlands.Henniart.CloseFieldsTwistCountFromGaloisQuotientStatement.{u, uW}`.
That statement is the implication from
`Langlands.Ramification.Local.CloseFieldsGaloisQuotientStatement.{u}` to
`Langlands.Henniart.CloseFieldsTwistCountStatement.{u, uW}`.

Let \(F\) be a p-adic field with absolute ramification index \(e\), let
\(X\) be the Laurent-series field over its residue field, and let
\(\Omega_X\) be the separable closure of \(X\). The premise gives a topological
group isomorphism
\(\varphi\colon G_F/G_F^e\simeq \mathrm{Gal}(\Omega_X/X)/G_X^e\) that carries
the image of \(G_F^v\) onto the image of \(G_X^v\) for \(0\le v\le e\). Here
\(G_F^v\) is the p-adic absolute upper group
`Ramification.Padic.absoluteUpperRamificationGroup F v`, and \(G_X^v\) is
`Ramification.Local.localAbsoluteUpperRamificationGroup X Ω_X v`. The
conclusion is \(T_F(k+1,s)=T_X(k+1,s)\) for \(s<(k+1)e\). Each count is the
extended cardinality of the set of unramified-twist orbits of irreducible
complex Weil classes of rank \(k+1\), Swan exponent \(s\) and torsion number
one.

The proof transports the counted orbits through \(\varphi\). It uses only
the filtration compatibility on \([0,e]\), with no residue-degree
compatibility.
[`HenniartCloseFieldsRouteStatement`](HenniartCloseFieldsRouteStatement.md),
[`CloseFieldsStatement`](../LocalFactor/Ramification/CloseFieldsStatement.md).

## Implemented proof

The final theorem chooses \(\varphi\) and its compatibility from the premise
at \(F\). It then applies `LocalNumerical.weilTwistIrreducibleCount_eq_of_galoisQuotient`.
The steps of that proof are below.

### 1. From Weil counts to Galois strata

The p-adic count `Numerical.weilTwistIrreducibleCount F k s` unfolds to the
`Set.encard` of `weilRefinedStratum F.Carrier (AlgebraicClosure F.Carrier) k s 1`,
using the instances of `F.canonicalTopologicalData`. The count on \(X\) is the
`Set.encard` of `weilRefinedStratum X Ω_X k s 1`. On each field,
`weilGaloisOrbitEquiv` is injective. It maps the Weil refined stratum onto
`galoisRefinedStratum _ _ k s 1` by
`weilGaloisOrbitEquiv_image_weilRefinedStratum`. So both counts are
`encard`s of Galois refined strata. The theorem concludes by
`Set.encard_congr` applied to a bijection between these two strata, which
is built in step 2.
[`HenniartGaloisDictionaryProof`](HenniartGaloisDictionaryProof.md).

### 2. Transport of Galois strata through a filtered quotient isomorphism

The section `GaloisTransport` concerns two nonarchimedean local fields
\(K_1,K_2\) with separable closures \(\Omega_1,\Omega_2\). It uses antitone
filtrations \(U_1,U_2\) of their Galois groups, a real number \(e\ge 0\) with
\(U_i(e)\) normal, and a topological isomorphism
\(\varphi\colon \mathrm{Gal}(\Omega_1/K_1)/U_1(e)\simeq\mathrm{Gal}(\Omega_2/K_2)/U_2(e)\).
This isomorphism carries the image of \(U_1(r)\) onto that of \(U_2(r)\) for
\(0\le r\le e\).

- *Characters.* A continuous character trivial on a normal subgroup descends
  to the quotient (`quotientCharacter`). `transferCharacter` composes it with
  \(\varphi^{-1}\) and the projection. If the image of a subgroup \(I\) is
  carried onto the image of \(J\), a character trivial on \(I\) transfers to
  one trivial on \(J\) (`transferCharacter_eq_one`).
- *Unramified characters.* Suppose \(U_i(0)\) is the absolute inertia
  subgroup. Then the compatibility at \(r=0\) matches the images of absolute
  inertia (`inertia_map_eq_of_filtration`). Since
  \(U_i(e)\le U_i(0)\), every unramified character is trivial on
  \(U_i(e)\). So transfer through \(\varphi\) and through
  \(\varphi^{-1}\) (`map_quotient_symm_eq`) gives mutually inverse maps
  between the unramified characters `galoisUnramifiedCharacters` of the two
  fields (`unramifiedEquiv`).
- *Twists and torsion numbers.* Classes are transported by
  `continuousIrreducibleQuotientTransport`, a rank-preserving bijection
  between continuous irreducible classes trivial on \(U_1(e)\) and those
  trivial on \(U_2(e)\). By `continuousIrreducibleQuotientTransport_twist`,
  twisting by an unramified character \(\chi\) commutes with this transport,
  with \(\chi\) replaced by its transfer
  (`galoisUnramifiedTwist_transport`). Hence the transport preserves the
  torsion number. That number is the number of unramified characters fixing
  the class (`galoisTorsionNumber_transport`). The transport also preserves
  and reflects equality of unramified-twist orbits
  (`galoisUnramifiedOrbitClass_transport_iff`).
- *Triviality parameters.* `trivialityParameters U c` is the set of
  \(r\ge 0\) with the class \(c\) trivial on \(U(r)\). For transported
  classes these sets agree (`trivialityParameters_transport`). For
  \(r\le e\) this follows from
  `continuousIrreducibleQuotientTransport_isTrivialOn_iff` and the
  compatibility at \(r\). For \(r>e\), both classes are trivial on
  \(U_i(r)\le U_i(e)\).
- *Swan exponents.* Assume that on each side `HasGaloisSwan ρ s` holds
  exactly when \(s\) is \((k+1)\) times the infimum of the triviality
  parameters of \(\rho\). Then the transport preserves the Swan exponent
  (`hasGaloisSwan_transport_iff`).
- *Strata.* `galoisRefinedStratumEquivOfQuotient` also assumes that each
  irreducible Galois class of rank \(k+1\) and Swan exponent \(s\) is trivial
  on \(U_i(e)\). Under this hypothesis it builds a bijection
  `galoisRefinedStratum K₁ Ω₁ k s f ≃ galoisRefinedStratum K₂ Ω₂ k s f`. It
  indexes both strata by the classes trivial on \(U_1(e)\) with Swan exponent
  \(s\) and torsion number \(f\). These classes map onto the first stratum by
  taking orbits. Taking the orbits of their transports maps them onto the
  second stratum; surjectivity uses the inverse transport. The two maps have
  the same fibres by the orbit statement above, so they induce the bijection.

### 3. The Galois-side hypotheses from the Weil side

The section `PullbackSwan` works over a nonarchimedean local field \(K\) with
a separably closed separable closure \(\Omega\). Absolute inertia lies in the
image of the Weil projection, by `Weil.Local.SepClosed.localInertiaInclusion`.
Let \(U\) be a filtration with \(U(r)\) inside absolute inertia for
\(r\ge 0\). Then the projection maps the preimage of \(U(r)\) in the Weil
group onto \(U(r)\). By `restrictClass_isTrivialOn_iff`, a Galois class is
trivial on \(U(r)\) exactly when its Weil pullback is trivial on that
preimage. So the triviality parameters of a Galois class and of its pullback
agree (`trivialityParameters_restrictClass`). `HasGaloisSwan` is defined
through the Weil pullback, which is unique by `galoisPullbackBijection`.
Hence the two Galois-side hypotheses of step 2 follow from their Weil
analogues for the preimage filtration (`hasGaloisSwan_iff_of_hasWeilSwan_iff`,
`isTrivialOn_of_hasGaloisSwan`).

### 4. The two fields

- *The Laurent-series field \(X\).* Use \(U_X(r)=G_X^r\). This filtration is
  antitone (`localAbsoluteUpperRamificationGroup_antitone`) and \(U_X(0)\) is
  absolute inertia (`Ramification.Local.absoluteUpperInertia`). The class
  last break is the infimum of the triviality parameters of the preimage
  filtration (`classLastBreak_eq_sInf_trivialityParameters`). So
  `hasWeilSwan_iff_eq_weilSwanConductor` gives the Swan hypothesis
  (`hasWeilSwan_iff_trivialityParameters`). `isTrivialAt_iff_of_hasWeilSwan`
  at the positive cutoff \(e\) gives triviality on the preimage of \(G_X^e\)
  for \(s<(k+1)e\) (`isTrivialOn_of_hasWeilSwan`).
- *The p-adic field \(F\).* Use the p-adic filtration
  \(U_F(r)=G_F^r\) of the premise. It is antitone
  (`Ramification.Padic.absoluteUpperRamificationGroup_antitone`), and
  \(U_F(0)\) is absolute inertia
  (`Ramification.HerbrandBridge.absoluteUpperCanonicalInertia`). The general
  Swan predicate `HasWeilSwan F.Carrier (AlgebraicClosure F.Carrier)` is, by
  definition, the p-adic one. The p-adic last break `lastBreak F A` is the
  infimum of the triviality parameters of the preimage of \(G_F^r\).
  `Numerical.hasWeilSwan_iff_eq_rank_mul_lastBreak` gives the Swan hypothesis
  (`padic_hasWeilSwan_iff_trivialityParameters`).
  `Ramification.HerbrandBridge.lastBreak_lt_iff_isTrivialAt` gives
  triviality on the preimage of \(G_F^e\) for \(s<(k+1)e\)
  (`padic_isTrivialOn_of_hasWeilSwan`).

Both sides use the filtration of the premise itself. So the proof needs no
comparison between the p-adic filtration on \(G_F\) and the general local
filtration `localAbsoluteUpperRamificationGroup F.Carrier (AlgebraicClosure F.Carrier)`.
The proof passes the normality of \(G_F^e\) explicitly as
`Ramification.Padic.absoluteUpperRamificationGroup_normal F e`. This subgroup
is stated for `Field.absoluteGaloisGroup F.Carrier`, whose group instance is
the automorphism group of `AlgebraicClosure F.Carrier` over `F.Carrier`
after unfolding.

[Transport through quotients](../Weil/Representation/FilteredQuotientClassTransport.md) ·
[Swan cutoff, general fields](HenniartLocalWeilSwanBreak.md) ·
[Swan cutoff, p-adic fields](HenniartWeilSwanBreak.md) ·
[Upper inertia, p-adic](../LocalFactor/Ramification/Herbrand/InertiaProof.md) ·
[Upper inertia, general](../LocalFactor/Ramification/Herbrand/LocalAbsoluteInertiaProof.md)

## Sources

The transport follows Henniart, *La conjecture de Langlands locale numérique
pour GL(n)*, Ann. Sci. ÉNS (4) 21 (1988), §5.1, printed p. 512
(`henniart-1988-numerical`). There the irreducible representations of the
specified dimension and Swan exponent below the cutoff correspond across
the filtered Galois quotient isomorphism, compatibly with unramified twists.
The same passage appears in the proof of Proposition `prop:LD` of
`numerical-LLC-route.tex` (`operator-numerical-llc-route-2026-11-16`),
lines 826–830. The upper numbering filtration is that of Serre, *Local
Fields*, Chapter IV §3 (`serre-1979-local-fields`).
