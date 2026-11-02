# Jacquet images of subrepresentations

Helper module for the juxtaposed case of Zelevinsky 1980, Proposition 4.6
(task 0c90f7e4-78fa-43fd-8736-238bb3e8617d). It contains no statement of its own
from the literature. It records standard consequences of the exactness of the
normalized Jacquet functor on smooth representations, which the Library proves
as `normalizedJacquetMap_exact`.

Let `π` be a representation of `GL_n` over a p-adic field and `C` a block shape.
Write `J` for the normalized Jacquet functor along `C`.

## Declarations

- `rangeEquivOfInjective f hf`: an injective intertwiner `f` gives an
  equivalence of its source with its range.
- `normalizedJacquetMap_injective`: if `σ` is smooth and `i : ρ → σ` is an
  injective intertwiner, then `J(i)` is injective. Proof: apply
  `normalizedJacquetMap_exact` to `i` followed by the quotient map onto
  `σ / range i`.
- `jacquetImage T C X`: the range of `J(X ↪ π)`, a subrepresentation of `J(π)`.
- `mem_jacquetImage`: `w` lies in the image exactly when `w` is the class of
  some `x ∈ X` in `J(π)`.
- `jacquetImage_mono`, `jacquetImage_top`: the map is monotone and sends `⊤` to `⊤`.
- `jacquetImageEquiv`: for smooth `π`, `J(X)` is equivalent to the image of `X`.
- `jacquetImage_inf`: for smooth `π`, the image of `X ⊓ Y` is the intersection of
  the images. The proof takes a class `w = [x] = [y]` with `x ∈ X` and `y ∈ Y`. The
  map `X → π/Y` factors as `X ↠ X/(X ⊓ Y) ↪ π/Y`. Since `[y]` maps to zero in
  `J(π/Y)`, the image of `[x]` in `J(X/(X ⊓ Y))` is zero, because the second
  factor stays injective after `J`. By exactness on `X ⊓ Y ↪ X ↠ X/(X ⊓ Y)`, the
  class of `x` in `J(X)` therefore comes from some `z ∈ X ⊓ Y`, and `w = [z]`.
- `jacquetImage_strictMono`: let `π` be smooth, and suppose every step quotient
  `Y/X` with `X ≤ Y` and `Y/X ≠ 0` has `J(Y/X) ≠ 0`. Then the map is strictly
  monotone. Proof: if `X < Y` have the same image, then `J(X) → J(Y)` is onto,
  because `J(Y) → J(π)` is injective. Hence every class in `J(Y/X)` is zero.
