# Multiplication on the glued scheme

`mulOpen` is the image of the original domain in `Gl ×_S Gl` under the
pair of original chart immersions. It contains all generic points of the
square, since every chart meets the original chart on the dense domain
of its partial translation and the projections are smooth.

Near a point of the square, keep a chart `i` for the first coordinate
and choose a section chart `d` for the second. Impose also that right
translation by `d` takes the first chart coordinate `x` into the domain
of the translation `τᵢ`. Both conditions can be imposed in the same
fibrewise dense open of section choices, by `chartCover`, strictness and
the base change lemmas. The local product of the chart points at `x`
and `y` is `mulG (τᵢ(xd), y)`. Where the products lie in the appropriate
original domains, associativity and translation compatibility identify it
with the original product. The agreement open contains the generic points.

The extension lemma gives `mulBar` over `S` and dense agreement identifies
its restriction to the original square with `mulG`. The use of a common
section to rewrite the product is the local multiplication step of BLR,
*Néron Models*, §5.3 Lemma 8, pp. 127–128, implemented here by open pieces.
