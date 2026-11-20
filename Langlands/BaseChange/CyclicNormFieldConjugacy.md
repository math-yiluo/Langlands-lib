# Ordinary and twisted conjugacy over cyclic field extensions

This module proves the uniqueness and twisted-conjugacy clauses of the cyclic
norm lemma over fields. `CyclicNormLemmaExistenceReductionStatement.{u,v}` is an
internal implication. Its sole premise, `FieldCyclicNormExistenceStatement.{u,v}`,
is the existence of a base-field representative for every norm in the field case.
`cyclicNormLemma_of_field_exists` combines the two proved field clauses with that
premise and applies the residue-field reduction. The implication leaves field
existence open.

## Uniqueness

Two associations of the same norm give a conjugator over the extension between
the two base-changed matrices. Expand extension coefficients in a basis over
the base field `F`. The two base-changed operators become the componentwise
actions of the original matrices on `dim_F E` copies of `Fⁿ`. The conjugator
then gives an isomorphism of those copies. `FiniteModuleCancellation` supplies
one `F`-linear intertwining equivalence, which yields the required conjugator
in `GL_n(F)`.

## Twisted conjugacy

For `δ` in `GL_n(E)`, write `D_δ(v) = δ σ(v)` on column vectors, with `σ` acting
on all coordinates. This is `F`-linear and `σ`-semilinear over `E`.
Given `g⁻¹ * N(δ) * g = N(δ')`, form the matrices
`c_i = cyclicNorm σ i δ * entrywiseAut (σ^i) n g * (cyclicNorm σ i δ')⁻¹`.
The norm conjugacy gives `c_l = c_0 = g`, and the product rule for the norm gives
`c_(i+1) = δ * entrywiseAut σ n c_i * δ'⁻¹`. Thus `D_δ` composed with `c_i`
equals `c_(i+1)` composed with `D_δ'`, including the transition back to `c_0`.

For a basis `b` of `E` over `F`, the matrix `B_(i,j) = σ^i(b_j)` is invertible.
The powers of `σ` up to `l - 1` are distinct, and Dedekind independence applies
to their restrictions to the basis because evaluation on a basis identifies
`F`-linear maps `E → E` with their lists of values. Applying `σ` to the entries
of row `i` gives the next row, with the last row going back to the first.
Let `B` act on `l` copies of `Eⁿ` by the same matrix of scalars. The row shift
then identifies componentwise `D_δ` with `D_δ` followed by the shift of copies.
The same holds for `δ'`, so `B⁻¹ * diag(c_i) * B` intertwines componentwise
`D_δ'` with componentwise `D_δ`. It is `E`-linear.

Over `F`, cancel the copies using the family of operators consisting of the
semilinear operator and all scalar multiplications by elements of `E`. The
resulting isomorphism intertwines the semilinear operators and is `E`-linear
because it commutes with those scalar multiplications. In matrix form it gives
`δ * entrywiseAut σ n x = x * δ'`, as required. This proof works for finite
base fields as well.

## Sources and provenance

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), Chapter 1, §1, Lemma 1.1, printed pp. 3–4, PDF pp. 17–18,
source ID `arthur-clozel-1989-base-change`, proves the field norm lemma. The Lean
field conjugacy arguments use cancellation of finite-dimensional modules.
Henniart and Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), §§I.2.1–I.2.2, printed pp. 10–12,
PDF pp. 18–20, gives the reduction to fields used in the final implication.
Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
