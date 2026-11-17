# Unipotence of smooth groups through geometric points

`Langlands.GroupScheme.SmoothUnipotentGeometricPointsStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field, write `kᵃ` for Mathlib's `AlgebraicClosure k`,
and let `G : GroupScheme (Spec (CommRingCat.of k))` satisfy `[Smooth G.X.hom]`
and `[IsAffineHom G.X.hom]`. Write `G_{kᵃ}` for the base change
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k kᵃ)))).obj G`.
The proposition says

```text
IsUnipotent G ↔
  ∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G_{kᵃ} n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of kᵃ))) ⟶ G_{kᵃ}.X),
    IsNilpotent ((ρ.rationalMatrix g : Matrix n n kᵃ) - 1)
```

In words, a smooth affine algebraic group over `k` is unipotent exactly when
every `kᵃ`-point of `G` acts by a unipotent matrix in every
finite-dimensional representation of `G_{kᵃ}`.

The ingredients are existing declarations, used without change.

- `Smooth G.X.hom` and `IsAffineHom G.X.hom` (Mathlib) say that the structure
  morphism `G.X.left ⟶ Spec k` is smooth and affine.
- `IsUnipotent G` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero fixed vector.
- `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along `Spec kᵃ ⟶ Spec k`.
- `MatrixRepresentation H n` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes from `H` to `GL_n`, a representation of `H` on `kᵃⁿ` with a
  chosen basis indexed by the finite type `n`.
- A morphism `g : Over.mk (𝟙 (Spec kᵃ)) ⟶ G_{kᵃ}.X` is a `kᵃ`-point of
  `G_{kᵃ}`, that is, an element of `G(kᵃ)`.
- `ρ.rationalMatrix g` (from
  [`MatrixRepresentationRationalPoints`](../MatrixRepresentationRationalPoints.md))
  is the invertible matrix with entries in `kᵃ` by which `g` acts in `ρ`.
  `IsNilpotent (M - 1)` says that the matrix `M` is unipotent.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 14.12, p.283: "A smooth algebraic group G is unipotent if and
  only if the elements of G(k^a) are unipotent."
- Definition 14.27, p.286: "Let G be an algebraic group over k. An element u
  of G(k) is unipotent if r(u) is unipotent for all finite-dimensional
  representations r of G." The following paragraph, p.287: "When k is
  perfect, this agrees with the definition in 9.19."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k." and "Recall that an element r of a ring is unipotent
  if r − 1 is nilpotent."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."
- p.13, after Proposition 1.26: "Therefore 'group variety' = 'smooth
  algebraic group'."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 14.12 on
printed p.283 and Definition 14.27 on printed p.286 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.13 or 135.

Milne's proof: as `G` is smooth, `G(kᵃ)` is dense in `G`. If its
elements are unipotent, then `G_{kᵃ}` is unipotent (14.10), and so `G` is
unipotent (14.9). Conversely, if `G` is unipotent, then so is `G_{kᵃ}`
(14.9), and the elements of `G(kᵃ)` are unipotent (14.10). This is
explanation only. The statement does not depend on that route.

## Derivation from the source

- **Smooth algebraic group.** Milne's algebraic group is a group scheme of
  finite type over `k`, affine by the Chapter 14 convention. The statement
  assumes `Smooth G.X.hom` and `IsAffineHom G.X.hom`. Smoothness gives local
  finite presentation and affineness gives quasi-compactness, so `G` is of
  finite type over `k`.
- **Elements of `G(kᵃ)` and their unipotence.** An element of `G(kᵃ)` is a
  `kᵃ`-point of the algebraic group `G_{kᵃ}` over `kᵃ`. Its unipotence is
  Definition 14.27 applied to `G_{kᵃ}` over the field `kᵃ`: it acts by a
  unipotent endomorphism in every finite-dimensional representation of
  `G_{kᵃ}`. Since `kᵃ` is perfect, this agrees with the notion of 9.19 used
  in Section 14b (the paragraph after 14.27). A finite-dimensional
  representation becomes a matrix representation once a basis is chosen, and
  an endomorphism is unipotent when its matrix minus the identity is
  nilpotent. The statement quantifies over all index types `n : Type`, all
  matrix representations `ρ` of `G_{kᵃ}` and all points `g`.
- **Algebraic closure.** Milne's `k^a` is an algebraic closure of `k`; the
  statement uses Mathlib's `AlgebraicClosure k`. Any two algebraic closures
  are isomorphic over `k`, so the choice does not matter.
- **Unipotent group.** Milne's definition is 6.45, which is `IsUnipotent`;
  its comparison is recorded in [`Reductive.Basic`](../Reductive/Basic.md).
- **Universes.** One universe `u` is used for `k` and the schemes, and the
  index types `n` live in `Type`, as in `MatrixRepresentation`. This is a
  formalization convention.
