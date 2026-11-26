# Descent of σ-discrete series on regular test functions

This module defines two propositions in `Langlands.BaseChange`.
`IsRegularSigmaLift` expresses the trace identity on concordant test pairs
with regular support and norm determinants on the ordinary side.
`SigmaDiscreteRegularDescentStatement` asks for an irreducible square-integrable
descent satisfying this identity.

## Regular σ-lifts

`IsRegularSigmaLift` has the setting of `IsSigmaLift`. The field `F` is a
topological field with `[IsTopologicalRing F]`, `E` is a commutative topological
`F`-algebra, and `n : ℕ`. Both `GeneralLinear n F` and `GeneralLinear n E` are
Hausdorff, locally compact and totally disconnected. The carriers `V` and `W`
are complex vector spaces. The arguments are `σ : E ≃ₐ[F] E`, `l : ℕ`, the
representations `π` of `GL_n(F)` on `V` and `τ` of `GL_n(E)` on `W` with
admissibility witnesses `hπ` and `hτ`, an intertwining isomorphism
`A : SigmaIntertwiner σ n τ`, and a constant `c : ℂ`.

The predicate requires `c ≠ 0`. With the Borel σ-algebras on the two groups, it
quantifies over every Haar measure `μF` on `GL_n(F)`, every Haar measure `μE`
on `GL_n(E)`, and all Schwartz–Bruhat functions `φ` on `GL_n(E)` and `f` on
`GL_n(F)`. The trace identity has the following hypotheses.

1. `AreConcordant σ l μF μE φ f`.
2. `IsSigmaRegularSupported σ l φ`, so each `δ` with `φ δ ≠ 0` is σ-regular.
3. `IsRegularSupported f`, so each `g` with `f g ≠ 0` is regular semisimple.
4. For every `g : GeneralLinear n F` with `f g ≠ 0`,
   `GeneralLinear.determinant g ∈ (Units.map (Algebra.norm F : E →* F)).range`.

The conclusion is
`twistedDistribution μE τ hτ A.toLinearMap φ = c * Character.distribution μF π hπ f`,
the equality \(\operatorname{tr}(\tau(\varphi)\circ A)=c\,\operatorname{tr}(\pi(f))\).
The determinant takes values in `Fˣ`. For a cyclic field extension the range
in the fourth hypothesis is the norm subgroup \(N_{E/F}(E^\times)\).
The same `c` works for every measure and test pair.

`IsSigmaLift` implies `IsRegularSigmaLift` by restricting the test pairs.
The converse for irreducible admissible representations in the cyclic local
field setting is a separate local argument. The ordinary member of a
norm-associated regular pair has norm determinant. The openness of
\(N_{E/F}(E^\times)\) in \(F^\times\) permits localized tests with ordinary
support in the determinant preimage of this subgroup. These tests can recover
the pointwise Shintani identity used in Henniart–Lemaire II.2.9 to pass to
all concordant test pairs.

## Descent statement

`SigmaDiscreteRegularDescentStatement.{u, v, uV, uW}` uses the quantifiers of
`SigmaDiscreteDescentStatement`. The base \(F\) is a nonarchimedean local field
of characteristic zero in `Type u`. The field \(E\) in `Type v` is an
`F`-algebra and topological ring with the `F`-module topology. The statement
quantifies over `σ : E ≃ₐ[F] E`, every degree `l` and every rank `n`, with
`hσ : IsCyclicAlgebra σ l` specifying a cyclic field extension of degree `l`
generated on the Galois side by `σ`. The instance block uses `hσ.1` for
`Module.Finite F E` and supplies the Hausdorff, locally compact and totally
disconnected instances on the two matrix groups.

For each complex vector space `W : Type uW` and each representation `ρ` of
`GL_n(E)` with `hρ : IsAdmissible ρ` and `IsSigmaDiscreteSeries σ n ρ`,
the statement takes every `A : SigmaIntertwiner σ n ρ`. It asserts that there
are a complex vector space `V : Type uV`, a representation `π` of `GL_n(F)`
on `V` with `hπ : IsAdmissible π`, and `c : ℂ` satisfying
`π.IsIrreducible`, `JacquetLanglands.IsSquareIntegrable π` and
`IsRegularSigmaLift σ l π hπ ρ hρ A c`. The carrier universe `uV` is arbitrary.
Square-integrability is modulo the center, with a unitary central character.

## Relation to the trace formula comparison

Henniart–Lemaire II.6.16–II.6.17 globalize the σ-discrete series using a twisted
pseudo-coefficient. In the ensuing comparison of the ordinary and twisted
simple trace formulas, they let the concordant test pair at the distinguished
place \(v_0\) vary over functions supported in the respective regular sets.

On the ordinary side, the cuspidal representations in the comparison are
determinant twists of one cuspidal representation by powers of the cyclic class
field character. Their local characters agree on matrices with norm determinant.
Arthur–Clozel §6.3, p. 57, uses this coincidence on the norm image at the
auxiliary place \(v_3\). At \(v_0\) the determinant support in
`IsRegularSigmaLift` makes each twist trace equal to the untwisted trace on the
given test function.
For general concordant functions, Henniart–Lemaire II.6.13, p. 129, uses
ordinary Weyl integration for the same equality because the ordinary orbital
integrals vanish at regular classes outside the group norm image. This step also
enters the argument of II.6.17 through its reference to II.6.13.

Henniart–Lemaire II.6.17 concludes the lift identity. Square-integrability
requires a further step using the lower cuspidal local component's genericity
and unitarity and the nonvanishing of its character on the regular elliptic set.
The character identity transports nonvanishing at a σ-elliptic class to its
regular elliptic norm. The ordinary specialization of the criterion in
Arthur–Clozel I, Lemma 2.11, uses this nonvanishing to rule out induction from
a proper Levi and gives square-integrability with unitarity. Compare the
application of the twisted criterion in §6.3, p. 56, and the return to the
arguments of the going-up direction on p. 57.

## Sources

- Henniart and Lemaire, *Changement de base et induction automorphe pour GLₙ en
  caractéristique non nulle*, Mém. SMF 124 (2011).
  I.2.5 (pp. 17–18) gives concordance and regular supports, II.2.7 (p. 67) defines
  the σ-lift, and II.2.9 (pp. 69–71) compares it with the Shintani identity.
  II.4.6 (p. 88) states the square-integrable descent conclusion, II.6.1
  (p. 118) refers to Arthur–Clozel for characteristic zero, and II.6.13 and
  II.6.16–II.6.17 (pp. 129–132) give the trace comparison and the local
  Weyl-integration step. Pages are printed, with PDF offset +8. Source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
  SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
  [Original text](https://www.numdam.org/item/10.24033/msmf.436.pdf)
- Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
  the Trace Formula* (1989), Chapter 1, Lemma 2.11 (pp. 18–19), Theorem 6.2 (b)
  (p. 51) and §6.3 (pp. 54–57). Pages are printed, with PDF offset +14. Source
  ID `arthur-clozel-1989-base-change`,
  SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
  [Original text](https://www.claymath.org/library/cw/arthur/pdf/30.pdf)
