# Twisted conjugates into `GL_n(O)` at an unramified field place

`Langlands.TraceFormula.InertTwistedCosetStatement.{u, v} : Prop` quantifies over
fields `F : Type u` and `E : Type v` with an `F`-algebra structure on `E`, an
automorphism `σ : E ≃ₐ[F] E`, and a natural number `l` satisfying
`IsCyclicAlgebra σ l`. This predicate makes `E` a finite reduced `F`-algebra
of dimension `l`, with `σ` of order `l` and with fixed field `F`. In the field
case, `E/F` is therefore cyclic Galois of degree `l` with generator `σ`.

The valuation subring `O : ValuationSubring E` is assumed to be a discrete
valuation ring. For each `x ∈ O`, `σ x` lies in `O`. The residue field
`IsLocalRing.ResidueField O` is finite, and some irreducible element `ϖ : O`
has image in `E` in the range of `algebraMap F E`.

For `n : ℕ` write `K = GL_n(O)` for
`Langlands.GeneralLinearGroup.integralSubgroup (Fin n) O.toSubring`. The
statement assumes `δ : GeneralLinear n E` lies in `K`, meaning that the
entries of both `δ` and `δ⁻¹` lie in `O`. It also assumes that the
characteristic polynomial of `cyclicNorm σ l δ = δ · δ^σ ⋯ δ^{σ^{l-1}}` has
unit discriminant in `O`. In Lean this is the equality of `O.valuation`
applied to the `Polynomial.discr` of the `Matrix.charpoly` with `1`, the
value of a unit in the multiplicative valuation.

The conclusion is that each `x : GeneralLinear n E` with `x⁻¹ * δ * x^σ ∈ K`
has a factorization `x = c * k` with `k ∈ K` and `c` in the `σ`-centralizer of
`δ`. Lean writes `x^σ` as `entrywiseAut σ n x`, which applies `σ` to each
entry. The centralizer is `twistedCentralizer (entrywiseAut σ n) δ`, the
subgroup of elements `c` satisfying `c⁻¹ * δ * c^σ = δ`.

## The unramified place

Identify `F` with its image in `E` and put `O_F = O ∩ F`. The restriction of
the valuation to `F` is discrete with the same value group, since the
uniformizer `ϖ` belongs to `F`. Thus `O_F` is a discrete valuation ring and
the ramification index is one. All powers of `σ` preserve `O` because `σ`
has finite order. The minimal polynomial over `F` of an element of `O` has
coefficients in `O_F`, since its roots are Galois conjugates in `O`.
Conversely, `O` is integrally closed in `E`, so `O` is the full integral
closure of `O_F` in `E`.

The integral closure of a discrete valuation ring in a finite separable
field extension is finite and torsion-free of rank the field degree, so
`O` is free of rank `l` over `O_F`. Reducing modulo the common uniformizer
gives residue degree `l`. The residue extension is separable because the
residue fields are finite. The integral closure is local, so there is a
single place above the place of `O_F`. These are the unramified inert
place conditions.

## Provenance

This is a derived statement. The last step of the proof of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), §17.8,
Lemma 17.8.3 (printed p. 464, continuing on p. 465), identifies the local
support in the stabilizer quotient with the image of the compact subgroup
at almost all places. This yields the source's value `1` for the integral
of the characteristic function of the integral points there. The integrand in
§18.5, (18.32) (printed p. 487), uses `x⁻¹ * δ * x^σ`, with its
centralizer as in (18.31).

The formal statement makes three changes to the source formulation.

- It concerns a single place and a single element.
- Its conclusion is the coset property underlying the value of the
  twisted orbital integral of the characteristic function of `K`.
- It replaces the almost-all-places qualifier with the integrality of
  `δ` and the unit discriminant of its norm's characteristic polynomial.

The ordered norm is the one in Henniart–Lemaire, *Changement de base et
induction automorphe pour GL_n en caractéristique non nulle* (2011),
§I.2.1 (printed pp. 10–11). Section I.2.2 (printed pp. 11–12) uses the
same norm and identifies the twisted orbit with the quotient by the
`σ`-centralizer.
