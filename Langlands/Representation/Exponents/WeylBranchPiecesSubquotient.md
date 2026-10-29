# Elementary laws for actual subquotients

Author: Worker 253.

The module `Langlands.Representation.Exponents.WeylBranchPiecesSubquotient`
proves closure laws for the predicate `WeylBranchPieces.IsSubquotient A X` of
[`WeylBranchPiecesStatement`](WeylBranchPiecesStatement.md): `X` is an actual
quotient of an actual subrepresentation of `A`. It also locates an
irreducible subquotient of a finitely filtered representation in one graded
piece.

The results are internal algebraic infrastructure. They are derived directly
from the definitions of subrepresentations, intertwining maps, character
twists and filtrations, and no literature source states them in this form.
All representations are complex linear, over arbitrary groups, with
independent carrier universes.

## Subquotient laws (namespace `Langlands.WeylBranchPieces`)

- `subtypeMap U`: the inclusion of an actual subrepresentation `U` of `A`,
  as an intertwining map from `U.toRepresentation` to `A`.
- `IsSubquotient.of_surjective`: a surjective intertwiner `A → Y` makes `Y` a
  subquotient of `A`, using the top subrepresentation.
- `IsSubquotient.refl`: every representation is a subquotient of itself.
- `IsSubquotient.of_equiv`: an intertwining equivalence `A ≃ Y` makes `Y` a
  subquotient of `A`.
- `IsSubquotient.trans`: a subquotient of a subquotient is a subquotient. If
  `U ≤ A` maps onto `Y` by `q`, and `U' ≤ Y` maps onto `Z` by `q'`, then the
  vectors `v ∈ U` with `q v ∈ U'` form an actual subrepresentation of `A`.
  It maps onto `Z` through `q` and `q'`.
- `IsSubquotient.of_equiv_right`, `IsSubquotient.of_equiv_left`,
  `IsSubquotient.of_surjective_left`: an equivalence of the target or the
  source, or a surjection onto the source, preserves being a subquotient.
- `IsSubquotient.comp`: restricting both actions along a group homomorphism
  `φ : H →* G` preserves being a subquotient. The same submodule and linear
  map are used.
- `IsSubquotient.of_comp_symm`: for a group isomorphism `e : G ≃* H`, if `Y` is a
  subquotient of `A ∘ e⁻¹`, then `Y ∘ e` is a subquotient of `A`.
- `IsSubquotient.twist`: twisting both actions by a common character
  `χ : G →* ℂˣ` preserves being a subquotient. The same submodule and linear
  map are used.

## Graded pieces (namespace `Langlands.WeylBranchPieces`)

These results use the finite natural filtrations `RepFunctorFiltration`,
their graded pieces `RepFunctorFiltration.graded` and the gluing relation
`IsGluedFrom` of `Langlands.Representation.Filtration.Definitions`. The
representations are actual functors `F : C ⥤ Rep ℂ G` over a group `G`, and
statements are made at one object `Y` of `C`.

- `exists_descend`: let `g : ρ → σ` and `f : ρ → τ` be intertwiners with `g`
  surjective and `ker g ≤ ker f`. Then there is an intertwiner `h : σ → τ`
  with `h (g x) = f x` for every `x`. It is the linear map
  `ker g`-descended from `f`, composed with the inverse of the first
  isomorphism `ρ ⧸ ker g ≃ σ`. The same construction is the private lemma
  `intertwiner_descends` of the Library module
  `Langlands.Representation.Filtration.SimpleSubquotientFactorProof`. That
  lemma cannot be imported, so it is repeated here.
- `isSubquotient_of_iso`: an isomorphism `P ≅ Q` in `Rep ℂ G` makes `Q.ρ` a
  subquotient of `P.ρ`.
- `isSubquotient_graded s Y j`: the `j`th graded piece of `s` at `Y` is a
  subquotient of `(F.obj Y).ρ`. The subrepresentation is step `j + 1` of
  the filtration, and the map is its projection onto the successive
  quotient.
- `exists_isSubquotient_graded s Y h`: if `X` is irreducible and `h` exhibits
  `X` as a subquotient of `(F.obj Y).ρ`, then `X` is a subquotient of
  `((s.graded j).obj Y).ρ` for some `j`. The graded pieces need not be
  irreducible.
- `IsGluedFrom.isSubquotient_piece h Y i`: if `F` is glued from `pieces`, then
  each `(pieces i).obj Y` is a subquotient of `F.obj Y`.
- `IsGluedFrom.exists_isSubquotient_piece h Y hX`: if `F` is glued from
  `pieces` and the irreducible `X` is a subquotient of `F.obj Y`, then `X` is
  a subquotient of `(pieces i).obj Y` for some `i`.

The proof of `exists_isSubquotient_graded` is a minimal-index argument. Let
`U ≤ F.obj Y` map onto `X` by `f`, and let `A i` be step `i` of the
filtration at `Y`. The property "`f` vanishes on `U ⊓ A i`" holds for
`i = 0`, because `A 0 = ⊥`. It fails for the last index, because
`A (last) = ⊤` and `X` is nonzero. So it holds at some `j` and fails at
`j + 1`. On `U ⊓ A (j + 1)`, the restriction of `f` is nonzero, so it is
surjective because `X` is irreducible. Its kernel contains the kernel of the
map to the graded piece `A (j + 1) ⧸ A j`, because `f` vanishes on
`U ⊓ A j`. By `exists_descend`, the restriction factors through the image of
`U ⊓ A (j + 1)` in the graded piece. That image is the required
subrepresentation of the graded piece. This is the argument of the Library
proof `Langlands.Representation.Filtration.SimpleSubquotientFactorProof`, but
here the graded pieces are not assumed simple. The two `IsGluedFrom` results
then follow from the natural isomorphisms between the graded pieces and the
permuted pieces.
