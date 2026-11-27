# The Galois criterion of semistable reduction over a strictly Henselian trait

`Langlands.AbelianScheme.StrictHenselianUnipotentInertiaSemiabelianStatement`
is the implication "unipotent inertia implies semistable reduction" of
Grothendieck's Galois criterion, stated over a strictly Henselian discrete
valuation ring. Over such a ring the inertia group is the whole Galois
group of the fraction field, so the hypothesis is asked of the finite étale
fundamental group of the fraction field itself. The module states the
proposition and does not prove it.

## Statement

The universe is `u`. The data are:

- a discrete valuation ring `W` that is a `HenselianLocalRing` with
  separably closed residue field (`IsSepClosed (ResidueField W)`), that is,
  a strictly Henselian discrete valuation ring;
- a fraction field `L` of `W` (`IsFractionRing W L`);
- an abelian scheme `A` over `Spec L`, that is, an abelian variety over
  `L`;
- a Néron model `N : NeronModel W L A` (from
  `Langlands/AbelianScheme/NeronModel.lean`), with its generic
  identification;
- a natural number `ℓ` with `Fact ℓ.Prime` and `IsUnit (ℓ : W)`, so that
  `ℓ` differs from the residue characteristic of `W`.

The hypothesis is asked for every algebraically closed field `Ω` in
universe `u`, every geometric point `s : Spec Ω ⟶ Spec L`, every family
`hu` of invertibility witnesses for the powers of `ℓ` in `Γ(Spec L, ⊤)`,
and every `g` in `FundamentalGroup s (geometricFiberFinite s)`. For all
these data the endomorphism

`Tate.PrimeAdic.rationalMonodromyRepresentation s (geometricFiberFinite s)
torsionFiniteEtale A ℓ hu g`

minus the identity is nilpotent. That is, every element of the finite étale
fundamental group of `Spec L` acts unipotently on the rational `ℓ`-adic
Tate module `V_ℓ` of `A`.

The conclusion is `N.HasGeometricSemiabelianReduction`, the predicate of
`Langlands/AbelianScheme/PotentialSemistableReductionStatement.lean`: the
identity component of the geometric special fibre of `N`, over the
algebraic closure of the residue field of `W`, is an extension of an
abelian variety by a split torus, the torus being the scheme-theoretic
kernel of a smooth surjective homomorphism onto the abelian variety.

The hypotheses and the conclusion have the shape of
`Langlands.AbelianScheme.UnipotentInertiaSemiabelianReductionStatement`
for the identity extension `W → W`. The base ring, fraction field,
abelian variety, prime and geometric monodromy data agree with those in
`Langlands.AbelianScheme.AbelianInertiaQuasiUnipotentStatement`. The
present hypothesis requires each `g` to act unipotently; the
quasi-unipotence statement concludes that for each `g` some positive power
`g ^ m` acts unipotently. The two conditions differ: for a constant
elliptic curve over `ℂ((t))` twisted by the quadratic extension
`ℂ((√t))`, an inertia element acts by `−1` on the rational Tate module,
which is not unipotent, while its square acts as the identity.

## Relation to the sources

Grothendieck, *Modèles de Néron et monodromie*, SGA 7 I, Exposé IX
(Lecture Notes in Mathematics 288, 1972), §3, cited by item number:

- 3.4.0: the formation of the Néron model commutes with passage to the
  strict henselization of the base, so semistable reduction may be tested
  over a strictly local trait.
- Proposition 3.5 (Galois criterion): for a trait `S`, semistable
  reduction (i) is equivalent to (iv), unipotence of echelon 2 of the
  inertia group `I` on `U = T_ℓ(A(K̄))`. The proof of (iv) ⇒ (ii) ⇒ (i)
  uses the orthogonality theorem 2.4 for the fixed part `U^I` and the toric
  part of the Tate module.
- Corollaire 3.8: these conditions are also equivalent to (vi), "the
  action of `I` on `U` is unipotent". The proof of (vi) ⇒ (iv) uses
  Corollaire 3.7 (an open subgroup of `I` acts unipotently of echelon 2)
  and the connectedness of unipotent algebraic groups in characteristic
  zero.

The Lean statement is the implication (vi) ⇒ (i) of Corollaire 3.8 when
`S = Spec W` is strictly local. Bosch, Lütkebohmert and Raynaud, *Néron
Models* (1990), §7.4, printed p. 184 (PDF p. 191), Theorem 6, state the
same equivalence of semi-abelian reduction with condition (b), a submodule
`T'` of `T_ℓ` stable under `I` with trivial action on `T'` and `T/T'`, and
refer to SGA 7 IX 3.5 for the proof. Their inertia group is
`I = Gal(K_s/K^sh)` (§7.4, printed p. 183).

The translation of the hypothesis is as follows. When `W` is strictly
Henselian it is its own strict henselization, so `L = K^sh`. For a
geometric point of `Spec L`, the finite étale fundamental group of
`Spec L` is the absolute Galois group `Gal(L_s/L)`, which is the inertia
group `I` of the sources. Its action on the Tate module of `A` is the
action of `I` on `T_ℓ(A(L_s))`. Unipotence on `V_ℓ = T_ℓ ⊗ ℚ_ℓ` is
unipotence on `T_ℓ`, since `T_ℓ` is a lattice in `V_ℓ`; Remarque 3.5.1 of
SGA 7 IX notes that the conditions depend only on the action on
`U ⊗ ℚ_ℓ`.

The conclusion is the geometric form of semistable reduction, as in
`UnipotentInertiaSemiabelianReductionStatement.md`. Since the residue
field of `W` is separably closed, a torus over it is already split, and
the identity component of the special fibre stays an extension of an
abelian variety by a torus over the algebraic closure.
