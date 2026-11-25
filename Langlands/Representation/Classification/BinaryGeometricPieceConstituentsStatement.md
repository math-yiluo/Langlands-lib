# First-block constituents of the geometric pieces of a binary product: auxiliary proposition

Module `Langlands.Representation.Classification.BinaryGeometricPieceConstituentsStatement`,
namespace `Langlands.Classification.BinaryGeometricPieces`. It serves the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`.

The module defines two predicates, `IsFirstBlockConstituent` and `IsMixedConstituent`, and
states the proposition `BinaryGeometricPieceConstituents`. Nothing is proved in this module;
the proposition is proved by `Langlands.Classification.LeftCuspidalDerivative.binaryGeometricPieceConstituents`
in module `Langlands.Representation.Classification.LeftCuspidalDerivative.Pieces`. It is an
internal step of the proof of the product clause of `LeftCuspidalDerivativeLemma`.

## Conventions

Fix a prime `p`, `F : PadicField.{uF} p` and `T : F.TopologicalData`. All representations are
smooth complex representations with carriers in `max uF uV`. For natural numbers
`a, k > 0` with `h : a + k = m`, `BlockShape.ofPair a k ha hk h` is the two-block shape `(a, k)`
of `m`; its block index type is literally `Fin 2` and its first block size is literally `a`.
`WeylBranchPieces.IsSubquotient X ρ` says that the representation `ρ` is (isomorphic to) a
subquotient of the representation `X` of the same group: the ambient representation comes
first. `SmoothRep.IsSubquotient ρ X` says the same with the constituent first. The restriction
of a representation `X` of a product Levi `GL_a × GL_k` to its first block is
`X.comp (MonoidHom.mulSingle _ 0)`, the pullback along the inclusion of `GL_a` as the first
factor.

## Definitions

* `IsFirstBlockConstituent F T Y ρ`, for `Y` on `GL_m(F)` and `ρ` on `GL_a(F)`, holds when
  either
  1. `m = a` (`h : m = a`) and `ρ` is a subquotient of the rank transport `T.castRank h Y`; or
  2. there are `k > 0`, `a > 0` and `h : a + k = m` such that `ρ` is a subquotient of the
     restriction to the first block `GL_a` of the normalized Jacquet module
     `T.normalizedJacquet (BlockShape.ofPair a k ha hk h) Y.representation`.

  No irreducibility is imposed on `ρ` by this definition. In the notation of Zelevinsky,
  case 2 says that `ρ` occurs as a `GL_a`-subquotient of `r_{(a,k),(m)}(Y)`.
* `IsMixedConstituent F T Y₁ Y₂ ρ`, for `Y₁` on `GL_{m₁}(F)`, `Y₂` on `GL_{m₂}(F)` and `ρ` on
  `GL_a(F)`, holds when there are `a₁, a₂ > 0` with `h : a₁ + a₂ = a` and irreducible
  representations `ρ₁` of `GL_{a₁}(F)` and `ρ₂` of `GL_{a₂}(F)` such that
  `IsFirstBlockConstituent F T Y₁ ρ₁`, `IsFirstBlockConstituent F T Y₂ ρ₂`, and `ρ` is a
  subquotient of `T.castRank h ((T.binaryNormalizedProductFunctor a₁ a₂).obj (ρ₁, ρ₂))`,
  the published binary normalized product `ρ₁ × ρ₂` transported to `GL_a`.

## The target `BinaryGeometricPieceConstituents`

The definition returns `Prop` and quantifies over every prime `p`, field `F`, topological
datum `T`, and the following data:

* `m₁, m₂, a, b > 0` with `h : a + b = m₁ + m₂`; write `B = BlockShape.ofPair m₁ m₂ h₁ h₂ rfl`
  (source shape on `GL_{m₁+m₂}`) and `C = BlockShape.ofPair a b ha hb h` (target shape);
* a minimal representative `w : MinimalRepresentatives B C` (the library's `W^{B,C}`:
  `w` is increasing on each block of `B` and `w⁻¹` on each block of `C`);
* block refinements `S` of `B` and `R` of `C` with
  `hS : IsIntersectionRefinement B C w S` and `hR : IsIntersectionRefinement C B w⁻¹ R`
  (the actual intersection subgroups `M_B ∩ w⁻¹(P_C)` etc. are the standard refined ones);
* representations `Y₁` of `GL_{m₁}(F)`, `Y₂` of `GL_{m₂}(F)` and `ρ` of `GL_a(F)`.

It asserts: if `Y₁` and `Y₂` have finite length, `ρ` is irreducible, and `ρ` is a subquotient of
the restriction to the first block `GL_a` of the geometric piece
`(geometricPieceFunctor T B C w S R hS.2.1 hR.2.1).obj (Y₁ ⊗ Y₂)` (the actual external tensor
product `FiniteTensor.externalSmoothObject (twoBlockFactors h₁ h₂ Y₁ Y₂)` of the Levi
`GL_{m₁} × GL_{m₂}`), then

* `w = 1` and `IsFirstBlockConstituent F T Y₁ ρ`, or
* `IsFirstBlockConstituent F T Y₂ ρ`, or
* `IsMixedConstituent F T Y₁ Y₂ ρ`.

`geometricPieceFunctor` is the library's piece `F_w = i ∘ w ∘ r` of the geometric lemma
(normalized refined Jacquet functor of `M_B`, conjugation transport, normalized refined
induction into `M_C`), as defined in `Langlands.Representation.Geometric.GeometricLemmaStatement`.

## Provenance and mathematical justification

This is an internal statement: a consequence, specialised to two-block shapes, of the
geometric lemma of Bernstein–Zelevinsky [BZ77, Lemma 2.12] in Zelevinsky's coordinate form
[Ze80, §1.2 Theorem and §1.6 Proposition, printed pp. 170–172]. It is not a verbatim statement
of either source.

For `B = (m₁, m₂)` and `C = (a, b)`, the representative `w ∈ W^{B,C}` corresponds to the
`2 × 2` matrix `(b_{ij})` of [Ze80, §1.6], with `a₁ = b_{11}`, `a₂ = b_{21}` the sizes of the
parts of the first `C`-block coming from the two `B`-blocks, `a₁ + a₂ = a`. The piece is
induced from the Levi `(GL_{a₁} × GL_{a₂}) × (GL_{b₁} × GL_{b₂})` of `M_C`, and its constituents
are glued from products `(σ₁ × σ₂) ⊗ (τ₁ × τ₂)` where `σᵢ ⊗ τᵢ` runs over the irreducible
constituents of `r_{(aᵢ, bᵢ)}(Yᵢ)` (normalized Jacquet modules; `r` is the identity when
`bᵢ = 0`). Because `w⁻¹` is increasing on the first `C`-block, the part from the first
`B`-block comes first, so the first-block factor is `σ₁ × σ₂` in this order. Hence an
irreducible `GL_a`-subquotient `ρ` of the first block is

* a constituent of `σ₂` with `a₁ = 0`, giving `IsFirstBlockConstituent Y₂ ρ`;
* a constituent of `σ₁` with `a₂ = 0`; then `a ≤ m₁` and the matrix is the one of the identity
  double coset, so `w = 1`;
* otherwise (`a₁, a₂ > 0`) a subquotient of `σ₁ × σ₂`, the mixed alternative.

The restriction to the first block of an external tensor product is a direct sum of copies
of the first factor, so its irreducible subquotients are those of the first factor; this is
why the definitions use restriction to `GL_a` rather than irreducible constituents of the
whole Levi.

## References

* [BZ77] I. N. Bernstein and A. V. Zelevinsky, Induced representations of reductive p-adic
  groups I, Ann. Sci. ENS (4) 10 (1977), 441–472, Lemma 2.12 (geometric lemma). Source ID
  `bernstein-zelevinsky-1977-induced-i`.
* [Ze80] A. V. Zelevinsky, Induced representations of reductive p-adic groups II. On
  irreducible representations of GL(n), Ann. Sci. ENS (4) 13 (1980), 165–210, §1.2 Theorem
  (the set `W^{β,γ}` and the functors `F_w`), §1.6 Proposition (coordinate form of the
  constituents of `F_w(ρ)`), printed pp. 170–172. Source ID `zelevinsky-1980-induced-ii`.
