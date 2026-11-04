# Geometric reductivity of reductive groups (Haboush's theorem)

`Langlands.GroupScheme.ReductiveGeometricReductivityStatement.{u} : Prop` states Haboush's
theorem that a connected reductive group over an algebraically closed field is geometrically
reductive.

## Statement

For every algebraically closed field `k : Type u`, every group scheme `G` over
`Spec (CommRingCat.of k)` with `IsPseudoReductive G`, every finite coordinate type `n`, every
coordinate representation `ρ : MatrixRepresentation G n` (an actual group-scheme homomorphism
`G ⟶ GL_n`) and every nonzero vector `v : n → k` with `ρ.IsFixedVector v`, there are a natural
number `d` and a polynomial `F : MvPolynomial n k` such that

1. `0 < d` and `F` is homogeneous of degree `d`;
2. `F` is `G`-invariant scheme-theoretically: for every scheme `T` over `Spec k`, every point
   `g ∈ G(T)` and every vector `x ∈ Γ(T, 𝒪_T)ⁿ`,
   `F(ρ(g) x) = F(x)`, where `F` is evaluated through the structure map
   `scalarMap T : k → Γ(T, 𝒪_T)` and `ρ(g) = ρ.pointMatrix T g`;
3. `F(v) ≠ 0`.

## Source and correspondence

Source: D. Mumford, J. Fogarty, F. Kirwan, *Geometric Invariant Theory*, 3rd enlarged edition
(1994), Appendix to Chapter 1, Section A (registered as `mumford-fogarty-kirwan-1994-git-3rd`):
definition (iii) on printed p. 191 and Theorem A.1.0, implication a) ⇒ b), on printed p. 192
(Haboush's theorem, reference [128] there).

- Definition (iii) calls `G` *geometrically reductive* if, for every rational representation
  `G → GL(V)` and every `0 ≠ v ∈ V^G`, there is `F ∈ (Symm^r V*)^G` for some `r > 0` with
  `F(v) ≠ 0`. Here `V = kⁿ` with the coordinate basis fixed by `ρ`; `Symm^r V*` is the space of
  homogeneous polynomials of degree `r` in the coordinates, so `F` is a homogeneous
  `MvPolynomial n k` of degree `d = r > 0`. A rational representation of the source is a
  homomorphism of algebraic groups `G → GL(V)`; here it is an actual group-scheme homomorphism
  `G ⟶ GL_n`.
- `v ∈ V^G` is expressed by the Library predicate `ρ.IsFixedVector v`, which fixes `v` under
  `ρ(g)` for all points `g ∈ G(T)` over all test schemes `T`.
- `G`-invariance of `F ∈ Symm^r V*` means invariance under the contragredient action, i.e.
  `F(g⁻¹ x) = F(x)` for all `g`; as `g` ranges over a group this is the same as `F(g x) = F(x)`
  for all `g`. It is stated scheme-theoretically on points over every test scheme and every
  `x ∈ Γ(T, 𝒪_T)ⁿ`, which is the invariance of `F` under the coaction of the coordinate ring
  and makes no reducedness assumption beyond the hypotheses on `G`.
- Theorem A.1.0 a) is "G is reductive". In the source (over an algebraically closed field, for
  linear algebraic groups) a reductive group is one whose radical is a torus. The Lean statement
  is restricted to connected `G` and uses the Library's `IsPseudoReductive G`: `G` is smooth,
  affine and connected, and every smooth connected unipotent normal closed subgroup of `G` is
  trivial. Over an algebraically closed field this is exactly a connected reductive group (see
  the docstring of `IsPseudoReductive`), so the Lean statement is the case of connected `G` of
  Theorem A.1.0 a) ⇒ b). The source's equivalence with c) and the strong form (degree a power
  of the characteristic) are not stated.

## Use

This is the deep input for proving `AffineHomogeneousQuotientReductiveStatement`: over an
algebraically closed field, an affine quotient `G/N` by a nontrivial smooth connected unipotent
subgroup `N` yields a fixed vector in a finite-dimensional representation of `G` that contradicts
geometric reductivity. Its proof is not part of this statement.
