# The Néron–Ogg–Shafarevich criterion for good reduction

`Langlands.AbelianScheme.NeronOggShafarevichStatement` is the implication
"unramified Tate module implies good reduction" of the criterion of Néron, Ogg and
Shafarevich, stated with the Library's finite étale fundamental groups and rational
prime-adic Tate modules. The module states the proposition and does not prove it.

## Statement

The universe is `u`. The data are:

- a discrete valuation ring `V` with fraction field `K` (`IsFractionRing V K`);
- an abelian scheme `B` over `Spec K`, that is, an abelian variety over `K`;
- a natural number `ℓ` with `Fact ℓ.Prime` and `IsUnit (ℓ : V)`, so that `ℓ` differs
  from the residue characteristic of `V`.

The hypothesis concerns every *strictly Henselian unramified* extension of `V`: a
discrete valuation ring `W` that is a `HenselianLocalRing` with separably closed
residue field, together with an algebra structure `V → W` that is a local
homomorphism and satisfies `(maximalIdeal V).map (algebraMap V W) = maximalIdeal W`.
For every such `W`, every fraction field `L` of `W` with a `K`-algebra structure for
which the square `V → W → L` and `V → K → L` commutes, every algebraically closed
field `Ω` in universe `u`, every geometric point `s : Spec Ω ⟶ Spec L`, every family
`hu` of invertibility witnesses for the powers of `ℓ` in `Γ(Spec L, ⊤)` and every `g`
in the finite étale fundamental group `FundamentalGroup s (geometricFiberFinite s)`,
the element

`Tate.PrimeAdic.rationalMonodromyRepresentation s (geometricFiberFinite s)
torsionFiniteEtale ((baseChange (Spec.algebraMap K L)).obj B) ℓ hu g`

is the identity. That is, the fundamental group of `Spec L` acts trivially on the
rational `ℓ`-adic Tate module `V_ℓ` of the base change of `B` to `L`. The finiteness
of geometric fibres is the published `geometricFiberFinite`, and finite étaleness of
the torsion is the published `torsionFiniteEtale`.

The conclusion is that there is an abelian scheme `G` over `Spec V` together with an
isomorphism of abelian schemes from its generic fibre
`(baseChange (Spec.algebraMap V K)).obj G` to `B`.

## Relation to the source

Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §7.4, printed p. 183
(PDF p. 190), fix a separable closure `K_s` of `K`, a strict henselization `R^sh`
of the valuation ring, with fraction field `K^sh`, and call
`I := Gal(K_s / K^sh)` the inertia group. Theorem 5 there states, for an abelian
variety `A_K` with Néron model `A` and a prime `ℓ ≠ char k`, the equivalence of
(a) abelian reduction, (b) `A` is an abelian scheme over `R`, (c) triviality of the
inertia action on every `ℓ^ν`-torsion group, and (d) the Tate module `T_ℓ(A_K)` is
unramified, that is, `I` acts trivially on it. The text after the proof (printed
p. 184) names the equivalence of (a) and (d) the criterion of Néron–Ogg–Shafarevich.
The statement here is the implication (d) ⇒ (b), with the conclusion expressed
without Néron models: an abelian scheme over `R` is the Néron model of its generic
fibre, so (b) gives an abelian scheme over `R` with generic fibre `A_K`.

The translation of (d) is as follows.

- The strict henselization `W = R^sh` of `V` is a strictly Henselian discrete
  valuation ring, the map `V → W` is local, and the maximal ideal of `V` generates
  that of `W`. Its fraction field `L = K^sh` is a `K`-algebra compatibly with `V`.
  The hypothesis is asked for every such `W`, so in particular for `R^sh`.
- For a geometric point `s` of `Spec K^sh`, the finite étale fundamental group of
  `Spec K^sh` at `s` is the absolute Galois group of `K^sh`, which is the inertia
  group `I` above.
- The Tate module of the source is that of `A_K`, with `I` acting through
  `Gal(K_s/K)`; it equals the Tate module of the base change to `K^sh` with its
  Galois action. The statement uses the rational module `V_ℓ = T_ℓ ⊗ ℚ_ℓ`.
  Since `T_ℓ` is torsion free, `I` acts trivially on `T_ℓ` if and only if it acts
  trivially on `V_ℓ`.

The hypothesis is required for every unramified strictly Henselian `W` and every
geometric point. The source's strict henselization is one such `W`, so the
hypothesis gives condition (d) of Theorem 5, and the conclusion follows from (b).
Neither strict henselizations nor Néron models appear in the Lean statement; a
proof has to supply them.
