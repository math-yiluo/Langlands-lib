# Semiabelian reduction from unipotent inertia

`Langlands.AbelianScheme.UnipotentInertiaSemiabelianReductionStatement` is
the implication "unipotent inertia implies semistable reduction" of
Grothendieck's Galois criterion of semistable reduction. It is stated with
the Library's finite étale fundamental groups, rational prime-adic Tate
modules and Néron models. The module states the proposition and does not
prove it.

## Statement

The universe is `u`. The data are:

- a discrete valuation ring `V` with fraction field `K`
  (`IsFractionRing V K`);
- an abelian scheme `B` over `Spec K`, that is, an abelian variety over
  `K`;
- a Néron model `N : NeronModel V K B` (from
  `Langlands/AbelianScheme/NeronModel.lean`), with its generic
  identification;
- a natural number `ℓ` with `Fact ℓ.Prime` and `IsUnit (ℓ : V)`, so that
  `ℓ` differs from the residue characteristic of `V`.

The hypothesis concerns every *strictly Henselian unramified* extension of
`V`, exactly as in `Langlands.AbelianScheme.NeronOggShafarevichStatement`.
Such an extension is a discrete valuation ring `W` that is a
`HenselianLocalRing` with separably closed residue field. It comes with an
algebra structure `V → W` that is a local homomorphism and satisfies
`(maximalIdeal V).map (algebraMap V W) = maximalIdeal W`. The hypothesis
is asked for every such `W` and every fraction field `L` of `W` with a
`K`-algebra structure for which the square `V → W → L`, `V → K → L`
commutes. It is also asked for every algebraically closed field `Ω` in
universe `u`, every geometric point `s : Spec Ω ⟶ Spec L`, every family
`hu` of invertibility witnesses for the powers of `ℓ` in `Γ(Spec L, ⊤)`,
and every `g` in `FundamentalGroup s (geometricFiberFinite s)`. For all
these data the endomorphism

`Tate.PrimeAdic.rationalMonodromyRepresentation s (geometricFiberFinite s)
torsionFiniteEtale ((baseChange (Spec.algebraMap K L)).obj B) ℓ hu g`

minus the identity is nilpotent. That is, every element of the fundamental
group of `Spec L` acts unipotently on the rational `ℓ`-adic Tate module
`V_ℓ` of the base change of `B` to `L`.

The conclusion is `N.HasGeometricSemiabelianReduction`, the predicate of
`Langlands/AbelianScheme/PotentialSemistableReductionStatement.lean`. The
identity component of the geometric special fibre of `N`, over the
algebraic closure of the residue field of `V`, is an extension of an
abelian variety by a split torus. The torus is the scheme-theoretic kernel
of a smooth surjective homomorphism onto the abelian variety.

## Relation to the sources

Grothendieck, *Modèles de Néron et monodromie*, SGA 7 I, Exposé IX
(Lecture Notes in Mathematics 288, 1972), §3, cited by item number:

- Définition 3.4: `A_K` has semistable reduction if the identity
  component of every fibre of the Néron model is an extension of an
  abelian scheme by a torus (Proposition 3.2 (i)).
- Proposition 3.5 (Galois criterion): for a trait `S`, semistable
  reduction is equivalent to (iv), unipotence of echelon 2 of the inertia
  group `I` on `U = T_ℓ(A(K̄))`. Here `I` is the inertia group after
  passage to the Henselization.
- Corollaire 3.8: these conditions are also equivalent to (vi), "the
  action of `I` on `U` is unipotent". The Lean statement is the implication
  (vi) ⇒ (i) of Corollaire 3.8.

Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §7.4, printed
p. 184 (PDF p. 191), Theorem 6, state the equivalence of semi-abelian
reduction with condition (b), a submodule `T'` of `T_ℓ` stable under `I`
with trivial action on `T'` and `T/T'`, and refer to SGA 7 IX 3.5 for the
proof. Silverberg and Zarhin, *Semistable reduction and torsion subgroups of
abelian varieties*, Ann. Inst. Fourier 45 (1995), §3, printed p. 405,
Theorem 3.3, give the criterion in a relative form and cite the same two
sources. In these references the hypothesis is unipotence of echelon 2.
Corollaire 3.8 shows that plain unipotence of every element suffices. A
group of unipotent endomorphisms of a finite-dimensional vector space is
unipotent as a group, by Kolchin's theorem.

The translation of the hypothesis is the one used in
`NeronOggShafarevichStatement.md`. A strict Henselization `R^sh` of `V`,
with fraction field `K^sh`, is one of the extensions `W` above. For a
geometric point of `Spec K^sh`, the finite étale fundamental group of
`Spec K^sh` is `Gal(K_s/K^sh)`, the inertia group `I` of the sources. Its
action on the Tate module of the base change of `B` to `K^sh` is the action
of `I` on `T_ℓ(B(K_s))`. Unipotence on `V_ℓ = T_ℓ ⊗ ℚ_ℓ` is unipotence on
`T_ℓ`, since `T_ℓ` is a lattice in `V_ℓ`. So the Lean hypothesis at
`W = R^sh` is condition (vi).

The conclusion is the geometric form of semistable reduction, as explained
in `PotentialSemistableReductionStatement.md` and
`RaynaudSemiabelianCriterionStatement.md`. Over the algebraic closure of
the residue field, the identity component of the special fibre remains an
extension of an abelian variety by a torus, and the torus splits. `N` is an
arbitrary Néron model of `B`. Néron models are unique up to unique
isomorphism, so the source's Néron model is one of them.

The proof in SGA 7 IX uses the orthogonality theorem 2.4 for 3.5 and the
monodromy theorem (Corollaire 3.7, proved in SGA 7 I, Exposé I) for 3.8.
Neither uses the semistable reduction theorem 3.6, which SGA 7 IX deduces
from 3.5 and 3.7.
