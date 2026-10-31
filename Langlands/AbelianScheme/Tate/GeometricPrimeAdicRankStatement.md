# Rank of the actual prime-adic Tate module at a geometric point

`Langlands.AbelianScheme.Tate.PrimeAdic.GeometricPrimeAdicRankStatement`
is a proposition-valued definition. It states the following existence and
dimension assertions, without proving them.

Let `S` be a scheme, `A : AbelianScheme S`, and `g : ℕ`. Assume
`A.HasRelativeDimension g`, the existing predicate
`SmoothOfRelativeDimension g A.X.hom`. Let `p` be a prime whose image in
`Γ(S, ⊤)` is a unit. For every algebraically closed field `Ω` in the
scheme's universe and every morphism `s : Spec Ω ⟶ S`, the conclusions are:

- There exists a `ℤ_[p]`-linear equivalence from the standard free module
  `Fin (2 * g) → ℤ_[p]` to `IntegralAt A p s`.
- `RationalAt A p s` is finite-dimensional over `ℚ_[p]`.
- Its `Module.finrank` over `ℚ_[p]` equals `2 * g`.

The first conclusion uses `Nonempty` to express existence of an equivalence.
It includes freeness and the specified finite rank. The separate
finite-dimensionality assertion prevents the numerical `finrank` equation
alone from being read as a finite-dimensionality statement.

## Actual modules and hypotheses

The targets are the published modules from
[`AbelianPrimeAdic`](AbelianPrimeAdic.md). Their torsion levels consist of
actual sections of the kernel of multiplication by `p ^ n` on `A`, over
`Over.mk s`. The integral module is their inverse limit with successive
multiplication-by-`p` transitions and the residue-defined `ℤ_[p]`-action.
The rational module is `ℚ_[p] ⊗[ℤ_[p]] IntegralAt A p s`. No independent
groups, bases, compatible finite-level identifications, or comparison
equivalences are inputs to this statement.

The chosen integer `g` is a hypothesis on the actual smooth structure
morphism, rather than a number attached to an unrelated module. Neither a
uniform dimension for every abelian scheme nor connectedness of `S` is
assumed. The unit condition on `p` is imposed on the base scheme; it excludes
the characteristic prime after passage to the specified field-valued point.
No quasi-separatedness or local noetherianity of `S` is required by the
statement.

## Source correspondence and relative specialization

The source is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*,
preliminary draft built 2012-02-08, Chapter X (10.1)–(10.3), printed
pp.141–142 (PDF pp.145–146). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
These original pages, together with printed p.143 (PDF p.147), were read
directly. No source-specific errata file was present in the available
Library.

The source works with a `g`-dimensional abelian variety over a field, with
prime different from the characteristic. It defines the Tate module using
separable-closure torsion points and notes in (10.2) that algebraic-closure
points give the same module away from the characteristic. In (10.3), it
asserts a noncanonical isomorphism with `ℤ_p^(2g)` and dimension `2g` after
rationalization. The tensor factors in the published Lean definition are
reversed from the source's convention, over the commutative ring `ℤ_[p]`.

This statement is a derived relative geometric-point formulation of that
field theorem. The source passage does not itself prove this formulation
for the Library's arbitrary-base bundled abelian schemes. A proof must
apply the field theorem to the actual pullback of `A` along `s`, relate its
dimension to the specified smooth relative dimension, transfer
invertibility of `p` to the point field, and identify its compatible torsion
sections and scalar actions with `IntegralAt A p s`. The existing
`AbelianScheme.baseChange` and `hasRelativeDimension_baseChange` give the
actual pullback and preservation of the relative-dimension predicate.
The existing `fibreLevelEquiv` identifies sections of the pulled-back
torsion kernels with the published levels as types; its existence alone
does not supply a compatible linear equivalence of the entire inverse
systems. These passage-to-the-fibre and module comparisons remain part of
the proof obligation.

## Status and scope

This module states the theorem target. It supplies no proof, chosen basis,
or chosen isomorphism. The claimed integral equivalence is algebraic and
generally noncanonical. The statement does not assert continuity of that
equivalence, compatibility with monodromy, or a trivialization of a Weil
pairing or of the Tate twist.

Finite étaleness of torsion, finite-level torsion rank, integral quotients
by powers of `p`, full and prime-to-modulus adelic freeness, and
restricted-product comparisons are not additional conclusions of this
target. They may provide prerequisites or later consequences through
separate proofs. No freeness assertion at the characteristic prime is made.
