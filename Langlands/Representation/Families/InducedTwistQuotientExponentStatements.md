# Exclusion and persistence of the inducing exponent in quotients of induced twists

Author: Worker 5120.

This module states three closed propositions in
`Langlands.Renard.AlgebraicFamily`:

- `InducedTwistQuotientExclusionStatement.{u,v}` (exclusion),
- `InducedTwistQuotientPersistenceStatement.{u,v}` (persistence),
- `InducedTwistQuotientExponentStatements.{u,v}`, their conjunction at the same
  universes.

It contains no proof. The propositions are derived intermediate targets for the
published `IrreducibleInducedTwistExistenceStatement`. The companion module
`IrreducibleInducedTwistExistenceReduction` proves that their conjunction
implies that statement.

## Common data

The ambient data are exactly those of `IrreducibleInducedTwistExistenceStatement`.
They are a connected reductive group `G` over a Hausdorff nonarchimedean local field `k`
of any characteristic, with canonical topology `RationalPointFamily.pointTopology`
on `G(k)`, and displayed local compactness and nonarchimedean-group hypotheses.
There is an actual rational parabolic `p : P ⟶ G`, a rational Levi `l : M ⟶ P`, and a
geometric unipotent radical `r : U ⟶ P`, with `subgroupMultiplication l r` an isomorphism.
The Levi points carry `leviPointTopology l hl` and the published derived instances. The
field and carrier universes `u` and `v` are independent.

In addition, both propositions quantify over every split component
`a : A ⟶ M` of `M` (`IsSplitComponent a`, Renard V.2.1). This is a central split torus
`A_M` with the published maximality property. The representations of `A_M(k)` used below
are restrictions along `rationalPoints.map a : A_M(k) →* M(k)`. Split components exist
and are unique up to isomorphism over `M` (`splitComponentStatement`), so quantifying
over all of them gives no stronger condition than fixing one.

For an irreducible admissible smooth complex representation `ρ` of `M(k)` and an
unramified character `ψ` in the published `Plancherel.unramifiedCharacters` of the
rational-character norms of `M`, write `ρψ = ρ.twist ψ` (actual `SmoothRep.twist`), and
`I_ψ = leviInductionFunctor p l r hp hr hl hmul` applied to `ρψ` (actual normalized
induction `i_P^G`). For an invariant subspace `S` of `I_ψ`, the quotient `I_ψ / S` is the
actual `SmoothRep.quotient`. Its normalized Jacquet module `r_P(I_ψ / S)` is the
published `leviJacquetFunctor p l r hp hr hl hmul`, a smooth representation of `M(k)`.

An *exponent* of a representation `π` of `A_M(k)` is a character
`χ : A_M(k) →* ℂˣ` with `IsGeneralizedEigencharacter π χ`. This means that there is a
nonzero vector `v` and one `n` with `(π(a) - χ(a))^n v = 0` for every `a ∈ A_M(k)`.

The generic locus is `Plancherel.rationalUnramifiedPrincipalOpen M _ f` for a nonzero
polynomial `f` in the canonical coordinates `rationalImageRank M` of the unramified
characters. It is the set of `ψ` at whose canonical coordinates `f` does not vanish.
This is the same form of genericity as `GenericInducedIrreducibilityStatement` in
`RenardGenericIrreducibilityStatements`. The polynomial may depend on `ρ` and `a`, but
not on `ψ`, `χ` or `S`.

## Exclusion

`InducedTwistQuotientExclusionStatement` asserts the following. For all data as above,
there is a nonzero polynomial `f` such that, for every `ψ` in its principal open locus,
the conditions below exclude the exponent:

- every exponent `χ` of the restriction of `ρψ` to `A_M(k)`,
- and every invariant subspace `S ≠ ⊥` of `I_ψ`,

together imply that `χ` is **not** an exponent of the restriction of `r_P(I_ψ / S)` to
`A_M(k)`. The case `S = ⊤` holds trivially, because the quotient is zero.

## Persistence

`InducedTwistQuotientPersistenceStatement` asserts the following. For all data as above,
there is a nonzero polynomial `f` such that, for every `ψ` in its principal open locus and
every invariant subspace `S ≠ ⊤` of `I_ψ`, some character `χ` of `A_M(k)` is both an
exponent of `ρψ` and an exponent of `r_P(I_ψ / S)`.

Neither proposition assumes supercuspidality, square integrability, splitness, positive
rank, or a residue-characteristic restriction. The case `P = G` is included.

## Provenance and why the propositions hold

The source is Takuya Konno, *A note on the Langlands classification and irreducibility of
induced representations of p-adic groups*, Kyushu J. Math. 57 (2003), 383–409. It is
registered as `konno-2003-langlands-classification`, file
`/home/taskhub/central-library/Konno--A note on the Langlands classification and irreducibility of induced representations of p-adic groups--2003.pdf`,
SHA256 `71931493382f2c8aa60734e27328db9a0f39c3af0b9c47bf746adcfa47fc0b42`.
The relevant part is Theorem 4.2 and its proof, printed pp. 402–405 (PDF pp. 20–23). The
proof compares the Jacquet modules of the irreducible submodule `τ` and of the quotient
`I_P^G(V_λ)/V_τ` with the Bruhat-filtration pieces (4.2). Claim 4.2.1 separates the
constituents of distinct pieces for generic `λ`. Claim 4.2.2 reduces irreducibility to
the vanishing of the Jacquet modules of the quotient.

Neither proposition appears verbatim in the source. They are derived formulations that
split the irreducibility argument into two halves, phrased with the central exponents
of `A_M(k)` and Zariski-generic parameters instead of Konno's small analytic
neighbourhood:

- Exclusion is the form, for the single parabolic `P`, of the separation in Claim 4.2.1.
  In the geometric lemma for `r_P(I_ψ)`, the identity piece is `ρψ`. Its `A_M`-exponent is
  `a ↦ ω_ρ(a) ψ(a)`, where `ω_ρ` is an `A_M`-exponent of the untwisted `ρ`. A piece for
  another double coset `P w P` has `A_M`-exponents of the form `a ↦ c(a^w) ψ(a^w)`. Here
  `a^w` is the conjugate of `a` by the representative, a point of `M(k)`, and `c` runs over
  a finite set of exponents of a Jacquet module of `ρ`, independent of `ψ`. The two
  exponents can coincide only when `ψ(a^w a⁻¹) = ω_ρ(a)/c(a^w)` for every `a`. For a
  character `ψ₀` whose real part lies in the open chamber of `P`, `ψ₀(a^w)` and `ψ₀(a)`
  have different moduli for some `a`. This is the nonzero displacement of a nonidentity
  piece. So `ψ ↦ ψ(a^w a⁻¹)` is a nonconstant monomial function, and each condition
  above defines a proper Zariski-closed set. Off the union of these finitely many sets,
  the `ω_ρψ`-part of `r_P(I_ψ)` comes only from the identity piece `ρψ`. For `S ≠ ⊥`,
  Frobenius reciprocity maps `r_P(S)` onto `ρψ`. Exactness of `r_P` and of the
  generalized eigenspaces then makes that part of `r_P(I_ψ / S)` vanish.
- Persistence follows from Konno's Theorem 4.2 together with Renard VI.8.4 (openness of
  the irreducibility locus, published as `InducedIrreducibilityOpenStatement`). Together these give a nonzero `f` such that `I_ψ` is
  irreducible on its principal open locus. There the only `S ≠ ⊤` is `⊥`. By Frobenius
  reciprocity, `ρψ` is a quotient of `r_P(I_ψ)`, so the central character of `ρψ` is a
  common exponent. The proof planned for this project avoids Theorem 4.2. It uses second
  adjointness to put `ρψ` into the opposite Jacquet module of `I_ψ / S`. A gallery of
  parabolics with a fixed cuspidal Levi then transports the exponent back to `r_P`,
  with rank-one generic irreducibility at each wall.

The conjunction is the exact hypothesis of
`irreducibleInducedTwistExistence_of_quotientExponentStatements`. The two propositions
quantify the polynomial separately, so they may be proved independently.

## Dependency boundary

The direct project imports are the published
`Langlands.Representation.Families.IrreducibleInducedTwistExistenceStatement`,
`Langlands.Representation.Category.Subquotients` (`SmoothRep.quotient`), and
`Langlands.Representation.Exponents.Jacquet` (`IsGeneralizedEigencharacter`).
No existing file or statement is changed. This module proves neither proposition, the
existence statement, nor any generic-isomorphism or Grothendieck-class identity.
