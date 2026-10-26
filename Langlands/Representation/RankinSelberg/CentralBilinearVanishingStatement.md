# Finite spectral support of twisted bilinear forms

This module defines
`Langlands.RankinSelberg.CentralBilinearVanishingStatement.{uF,uV,uW}`
as a proposition. It gives an internal, derived formulation of the residual
bilinear obstruction in JPSS §2.10, printed p.398. It does not prove the
proposition.

Worker 189 prepared the statement and this explanation. The assertion follows
the feasibility example supplied by Worker 353 in the parent task's shared
draft revision 3; that unreviewed example is a development aid, not accepted
proof evidence.

## Exact quantifiers and conventions

The arguments are `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p`, `T : F.TopologicalData`, and `n : ℕ`.
Thus the field is a finite extension of `ℚ_p` in its own universe, and the
group is

```text
G = Langlands.GeneralLinear (n + 1) F.Carrier.
```

The definition installs `T.topology`, with no requirement that the supplied
data be definitionally the canonical data. The group has the resulting matrix
and units topology. Write `q = T.residueCardinality` and
`abv = normalizedAbsoluteValue T`. These are the existing residue cardinality
and normalized absolute value, with uniformizer absolute value `q⁻¹`.

For every `V : Type uV` and `W : Type uW`, each with an `AddCommGroup` and a
`Module ℂ` instance, and every pair

```text
ρ : Representation ℂ G V
σ : Representation ℂ G W,
```

the assumptions, in order, are

```text
IsAdmissible ρ
Module.Finite (MonoidAlgebra ℂ G) ρ.asModule
IsAdmissible σ
Module.Finite (MonoidAlgebra ℂ G) σ.asModule.
```

The existing `Langlands.IsAdmissible` means smoothness and finite-dimensional
fixed vectors for every open subgroup. Smoothness means that each vector is
fixed by some open subgroup. The two `Module.Finite` hypotheses mean finite
generation over the actual complex group algebra via the representations,
not finite-dimensionality of the carriers over `ℂ`. No topology is placed on
either carrier. The three universe levels `uF`, `uV`, and `uW` are independent.

The conclusion has the precise order

```text
∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint q s ∉ E →
  ∀ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ,
    (∀ g v w,
      β (ρ g v) (σ g w) = determinantWeight abv g (-s) * β v w) →
    β = 0.
```

Here `g` ranges over all of `G`, `v` over `V`, and `w` over `W`. The curried
linear map is a complex bilinear form. Its equality with zero is equality of
bilinear maps, hence vanishing on every pair of vectors. The existing weight
is `(abv (Matrix.det g.val) : ℂ) ^ (-s)`, and
`spectralPoint q s = (q : ℂ) ^ (-s)`. Thus exceptions are finitely many
spectral values, not finitely many exponents `s`.

The exceptional set may depend on the field, supplied topological data, rank,
carriers, and representations. It is chosen before both `s` and `β` and works
for every form with the stated covariance. The definition does not choose a
central polynomial or impose one as an assumption.

There are no hypotheses of irreducibility, Whittaker type, nonzero carrier,
scalar central character, finite length, or a supplied central decomposition.
Rank one is included by `n = 0`. A zero carrier is allowed on either side;
then every bilinear form is zero. Rank zero is excluded by the positive rank
`n + 1`.

## Original sources and derived scope

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics **105** (1983),
367–464, §2.1, pp.385–386, and §2.10, pp.396–398.
The registered source is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed page equals one-based PDF page plus 365; the cited pages were read
visually.

JPSS §2.1 starts with admissible representations of finite type and defines
Whittaker type by the additional one-dimensional functional condition.
The proposition on p.396 concerns twisted invariant trilinear forms on
Whittaker models and Schwartz–Bruhat functions. On p.398 the difference
remaining after restriction to functions vanishing at zero has the form
`γ(W,W') Φ(0)`. Its bilinear coefficient satisfies exactly the simultaneous
covariance with `|det g|^(-s)` used here. The source eliminates this residual
coefficient outside finitely many values of `q^(-s)`, phrasing the obstruction
in terms of a twisted contragredient.

The present statement isolates that residual bilinear assertion on arbitrary
admissible representations of finite type. Dropping the Whittaker-functional
condition and allowing zero carriers are internal derived generality. JPSS
does not state this particular formulation or its operator-polynomial proof.
The statement concerns p-adic fields; the source allows arbitrary
non-Archimedean local fields. It supplies no assertion about the other
mirabolic or trilinear steps of JPSS §2.10.

I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n,F),
where F is a non-archimedean local field*, Russian Mathematical Surveys
**31** (1976), no.3, 1–68, §2.1, p.15, gives the smoothness and admissibility
conventions: open vector stabilizers and finite-dimensional fixed spaces for
open subgroups, with no topology on the vector space. The registered source
is `bernstein-zelevinsky-1976-representations-gln`, retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`,
SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Printed and one-based PDF pages agree. Pages 15–17 and 23–25 were read;
the Frobenius and coinvariant results on pp.23–25 are context, not
prerequisites of this statement. No matching source erratum note was found
in the checked project and Library notes or registered literature index.
Both retained source fingerprints were verified.

## Proof obligations

Only the proposition is defined here. A proof must derive its finite
exceptional set from the displayed hypotheses. One polynomial route, which
avoids the GL finite-length theorem and eigenvalue decomposition, has the
following obligations.

1. Use finite group-algebra generators and smoothness to evaluate intertwiners
   injectively in a finite product of finite-dimensional open fixed spaces.
   Admissibility then makes the full equivariant endomorphism algebra finite
   dimensional. Each central action, as an element of that algebra, satisfies
   a monic complex polynomial. Equivalently, one can use a common open
   stabilizer of the generators, show its fixed space is preserved by the
   central operator, and propagate a polynomial annihilator from the
   generators to the whole representation using centrality.
2. Choose the scalar matrix `z = ϖ⁻¹ I` for a uniformizer normalized by the
   supplied `T`. Verify centrality, invertibility, and
   `abv (det z) = q^(n+1)`, then justify the complex-power identity
   `determinantWeight abv z (-s) = (spectralPoint q s)^(n+1)`.
   The normalization and complex-power steps must be proved for the supplied
   data, rather than assumed from a different absolute value.
3. For `A = ρ z` and `B = σ z`, derive a monic annihilator `P` of the tensor
   operator `A ⊗ B` from their integrality. It must be nonzero even when a
   carrier is zero. Lift the bilinear form to a linear functional on the
   tensor product. Central covariance implies
   `P((spectralPoint q s)^(n+1)) * β v w = 0` for all `v,w`.
4. Pull the finite root set of `P` back through the positive power `n+1`.
   Each equation `x^(n+1) = c` has finitely many roots because
   `X^(n+1) - C c` is nonzero; positivity of the rank is essential here.
   Choose the union of these root sets before `s` and `β`. Outside it the
   scalar in the previous equation is nonzero, forcing `β = 0`.

These are obligations for a successor proof, not assumptions or proved
conclusions of this module. The only import is the existing
`Langlands.Representation.RankinSelberg.AnalyticStatement`, which supplies
the normalization, spectral, determinant-weight, and representation
definitions. The statement has no dependency on a feasibility prototype or
the implementation of any proposed proof helper.
