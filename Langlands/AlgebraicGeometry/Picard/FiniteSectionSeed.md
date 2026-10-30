# Finite section seeds separating a point and its tangent vectors

This module defines one Prop-valued predicate,
`Langlands.AlgebraicGeometry.Picard.IsFinitePointTangentSectionSeed`. It records a finite
family of actual line-bundle sections that separates a chosen point `z` from the other
rational points and from the nonzero rational tangent vectors at `z`. It is the
section form of the first step of Milne's proof of Theorem 7.1. The definition asserts
no existence; it supplies a reusable interface for the later existence statement.

## The definition

Fix a universe `u`, a field `K : Type u`, a scheme `X : Scheme.{u}`, a morphism
`p : X ⟶ Spec K` and a morphism `z : Spec K ⟶ X`. The family consists of `n : ℕ`, line
bundles `L : Fin n → LineBundle X` and sections
`s : (i : Fin n) → GlobalSections (L i).obj`. The predicate
`IsFinitePointTangentSectionSeed p z n L s` is the conjunction of:

1. for every `i`, `VanishesAlong (L i) z (s i)`: every section vanishes at `z`;
2. for every `i`, there is a morphism `y : Spec K ⟶ X` with `IsRationalPoint p y` and
   `¬ VanishesAlong (L i) y (s i)`: no section vanishes at every rational point;
3. for every `x : Spec K ⟶ X` with `IsRationalPoint p x` and `x ≠ z`, some `i` has
   `¬ VanishesAlong (L i) x (s i)`;
4. for every `t : Spec K[ε] ⟶ X` with `IsNonzeroTangentVectorAt p z t`, some `i` has
   `¬ VanishesAlong (L i) t (s i)`.

All notions are the published ones, used unchanged: `LineBundle` from
`Langlands.AlgebraicGeometry.Picard.LineBundle`, `GlobalSections` from
`Langlands.AlgebraicGeometry.Modules.TensorSections`, and `IsRationalPoint`,
`VanishesAlong` and `IsNonzeroTangentVectorAt` from
`Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`. `VanishesAlong L f s` says
that the pullback of `s` along `f` is the zero global section. A rational point is a
section `x` of `p` (`x ≫ p = 𝟙`). A nonzero rational tangent vector at `z` is a
`K[ε]`-point over `K` that restricts to `z` along `ε ↦ 0` and differs from the constant
`K[ε]`-point at `z`. Here `K[ε]` is `DualNumber K`.

The point `z` is not assumed rational here. The existence statement will take `z` to
be the unit of a group scheme, which is rational. The family `n, L, s` is a parameter;
nothing asserts that a seed exists. The predicate builds in no scheme-theoretic divisor,
prime divisor, regularity, projectivity, ampleness, supplied separating line bundle or
certificate.

## The case `n = 0`

The family may be empty. Then clauses 1 and 2 hold vacuously. Clause 3 then says that
every rational point equals `z`, and clause 4 says that there is no nonzero rational
tangent vector at `z`. This does not say that `z` is rational, or that any rational
point exists. If `p` has no rational points, clause 3 holds vacuously, while `z` is not
rational. Only under the extra hypothesis `IsRationalPoint p z` does clause 3 say that
`z` is the unique rational point.

Allowing `n = 0` is essential in dimension zero. More generally, suppose every rational
point of `X` equals `z`, possibly because there are none. Then clause 2 for an index `i`
needs a rational `y`, which must be `z`, with `¬ VanishesAlong (L i) z (s i)`. This
contradicts clause 1, so no nonempty family is a seed. Take `X = Spec K` with `p = 𝟙`
and `z = 𝟙`. Here `z` is rational, and the empty family is a seed. Clause 3 holds
because a rational point `x` satisfies `x = x ≫ 𝟙 = 𝟙 = z`. A tangent vector `t` over `K` satisfies
`t = t ≫ 𝟙 = dualNumberProjection K`, which is the constant `K[ε]`-point at `z`, so
clause 4 holds vacuously. A smooth, geometrically connected group scheme of dimension
zero over an algebraically closed field is isomorphic over `K` to this example (a
standard fact, not formalized here). An existence statement for such group schemes
therefore needs `n = 0`. This matches Milne: a zero-dimensional variety has no prime
divisors, so his finite set is empty, and the empty intersection is `A = {0}`.

## Source and correspondence

J. S. Milne, *Abelian Varieties* (corrected author version, January 2, 2022; registered
as `milne-abelian-varieties-1986-author-2022`), proof of Theorem 7.1, p.11. The retained
errata (`milne-abelian-varieties-1986-errata-2026-10-25`) says its corrections are
incorporated in that version and none concerns Sections 6 or 7. Over an algebraically
closed field, Milne first chooses a finite set `{Zᵢ}` of prime divisors on the abelian
variety `A` with:

- (a) `⋂ Zᵢ = {0}`;
- (b) for every `t ∈ T₀(A)` there is a `Zᵢ` with `t ∉ T₀(Zᵢ)`. The printed text has
  `tᵢ ∉ T₀(Zᵢ)`; the subscript is a misprint, since `t` is fixed. Read literally,
  `t = 0` lies in every `T₀(Zᵢ)`, so `t` must be a nonzero tangent vector. The
  very-ampleness criterion (b) quoted on the same page is read the same way.

This predicate is a derived section formulation of (a) and (b), together with
properness of each zero set. It is not a literal transcription:

- Each prime divisor `Zᵢ` is replaced by a line bundle `L i` with a global section
  `s i`. In Milne's argument these would be `L(Zᵢ)` and its canonical section.
- Property (a) gives `0 ∈ Zᵢ` for every `i`, which becomes clause 1. Its other half,
  that no point other than `0` lies in every `Zᵢ`, becomes clause 3, tested only on
  rational points. Milne's points are closed points; over an algebraically closed field
  these are the rational points of a scheme of finite type. Over a general field the
  predicate tests only rational points.
- Property (b), restricted to nonzero `t`, becomes clause 4. Here "`t ∈ T₀(Zᵢ)`" is read
  as "`s i` vanishes along the `K[ε]`-point `t`", and `T₀(A)` is replaced by the
  `K[ε]`-points of `X` over `K` restricting to `z`.
- Clause 2 records properness of each zero set by an explicit rational point outside it.
  Over an algebraically closed field this is how properness of a closed subset shows up.
  A prime divisor is automatically a proper subset. Milne uses this when he says that the
  sets `{b₁ | Z₁,b₁ passes through b}` and `{b₁ | Z₁,−a₁−b₁ passes through b}` are proper
  closed subsets of `A`.

No comparison between this predicate and prime or Cartier divisors is proved here. This
includes the comparison of zero loci with closed subsets and of vanishing along
`K[ε]`-points with tangent spaces. Producing such sections from prime divisors needs
local factoriality of smooth schemes, which is a separate obligation; defining this
predicate does not discharge it.
