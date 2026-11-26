# Quasi-unipotence of inertia on Tate modules of abelian varieties

`Langlands.AbelianScheme.AbelianInertiaQuasiUnipotentStatement` is
Grothendieck's monodromy theorem for abelian varieties over the fraction
field of a strictly Henselian discrete valuation ring, stated element by
element. It is stated with the Library's finite étale fundamental groups
and rational prime-adic Tate modules. The module states the proposition and
does not prove it.

## Statement

The universe is `u`. The data are:

- a discrete valuation ring `W` that is a `HenselianLocalRing` with
  separably closed residue field (`IsSepClosed (ResidueField W)`), that is,
  a strictly Henselian discrete valuation ring;
- a fraction field `L` of `W` (`IsFractionRing W L`);
- an abelian scheme `A` over `Spec L`, that is, an abelian variety over
  `L`;
- a natural number `ℓ` with `Fact ℓ.Prime` and `IsUnit (ℓ : W)`, so that
  `ℓ` differs from the residue characteristic of `W`;
- an algebraically closed field `Ω` in universe `u` with a geometric point
  `s : Spec Ω ⟶ Spec L`;
- a family `hu` of invertibility witnesses for the powers of `ℓ` in
  `Γ(Spec L, ⊤)`;
- an element `g` of the finite étale fundamental group
  `FundamentalGroup s (geometricFiberFinite s)`.

The conclusion is that there is `m > 0` such that

`Tate.PrimeAdic.rationalMonodromyRepresentation s (geometricFiberFinite s)
torsionFiniteEtale A ℓ hu (g ^ m)`

minus the identity is a nilpotent endomorphism. In words, `g ^ m` acts
unipotently on the rational `ℓ`-adic Tate module `V_ℓ(A)`. Equivalently,
`g` acts quasi-unipotently: all its eigenvalues on `V_ℓ(A)` are roots of
unity. The finiteness of geometric fibres is the Library's
`geometricFiberFinite`, and finite étaleness of torsion is the Library's
`torsionFiniteEtale`.

## Relation to the sources

SGA 7 I (*Groupes de monodromie en géométrie algébrique*, directed by
A. Grothendieck, Lecture Notes in Mathematics 288, 1972), Exposé I
(*Résumé des premiers exposés de A. Grothendieck*, written by P. Deligne),
with page numbers of the exposé:

- 0.0.7 (p. I-2) calls an endomorphism `T` of a finite-dimensional vector
  space quasi-unipotent if its eigenvalues are roots of unity, that is, if
  `(T ^ N - 1) ^ M = 0` for some `N ≥ 1` and `M ≥ 1`. The Lean conclusion
  is this condition with `N = m`.
- 0.3 (pp. I-3 and I-4) fixes a Henselian trait `S` with generic point
  `η` and defines the inertia group `I` as the kernel of
  `Gal(η̄/η) → Gal(s̄/s)`. When the residue field is separably closed,
  `I` is the whole Galois group `Gal(η̄/η)`.
- Théorème de monodromie 1.2 (p. I-6) concerns a scheme `X` of finite type
  over `η` and an `ℓ`-adic cohomology space `H` of `X_η̄` of one of the types
  listed in 0.1 (p. I-2), among them (0.1.2), `X` proper. Every element of
  `I` acts quasi-unipotently on `H`, provided a condition (`*ℓ`) on the
  residue field holds. Variante 1.3 (p. I-6) removes that condition.

For an abelian variety `A` over `η`, take `X = A` (proper) and
`H = H¹(A_η̄, ℚ_ℓ)`. SGA 7 I, Exposé IX, in the proof of Corollaire 3.7,
gives the Galois-equivariant isomorphism
`H¹(A_K̄, ℤ_ℓ) ≅ Hom(T_ℓ(A(K̄)), ℤ_ℓ)`. So `V_ℓ(A)` is the contragredient
of `H`, and an element acts quasi-unipotently on one exactly when it does
on the other. Corollaire 3.7 of Exposé IX states the result in the stronger
form that an open subgroup of `I` acts unipotently, of echelon 2, on
`T_ℓ(A(K̄))`. In a profinite group every element has a positive power in a
given open subgroup, so Corollaire 3.7 also gives the Lean statement.

The translation to the Lean data is as follows.

- `S = Spec W` is a strictly Henselian trait and `η = Spec L`.
- For a geometric point `s` of `Spec L`, the finite étale fundamental group
  of `Spec L` at `s` is the absolute Galois group `Gal(L^sep/L)`. Since the
  residue field of `W` is separably closed, this is the inertia group `I`
  of the source.
- The Tate module is the Library's rational prime-adic Tate module of `A`
  at `s`, with the monodromy representation
  `Tate.PrimeAdic.rationalMonodromyRepresentation` from
  `Langlands/AbelianScheme/Tate/PrimeMonodromy.lean`.

The source proves the theorem for every Henselian trait, with `I` the
inertia group. The Lean statement is the case of a strictly Henselian
trait, for an abelian variety.
