# Universal tensor values of extension-field characters

Author: Worker 706; verified and documented for the exact descent proof by
Worker 1366. All constructions here are derived internal interfaces built
from the actual Library coordinate algebra, characters and point maps.

Let `G/k` be any affine group scheme over a field, and write
`Coord G = CharacterUnits.Coord G`. For a field extension `E/k`,
`tensorPoint G E` extends the existing universal point of `G` along the
right inclusion into `E ⊗[k] Coord G`. Evaluating a character of the actual
base change `G_E` at this point using the existing `valueE` gives
`tensorValue G E ψ`, a unit of that tensor algebra.

For a commutative `E`-algebra `D` with the compatible `k`-algebra structure,
and a point `y` of `G` over `D`, `tensorEval G E D y` is the `E`-algebra
map from the tensor algebra to `D`. It multiplies an extension coefficient
by the value of the coordinate under `Lie.pointCoordinates G y`.
`tensorEval_tensorPoint` shows that it takes the universal tensor point to
`y`, by injectivity and naturality of the coordinate comparison.

`tensorValue_eval` then applies naturality of the actual character values:
evaluating the universal tensor unit by `tensorEval` gives `valueE ψ D y`.
`tensorEval_naturality` establishes compatibility with maps of test
algebras, by tensor extensionality and coordinate naturality.

For a finite Galois intermediate field `L` of an ambient extension `K/k`,
`tensorEval_compare` compares evaluation of an `L`-tensor before and after
extension from a test `L`-algebra `B` to `K ⊗[L] B`. It identifies the two
actual composites of algebra maps, using tensor extensionality and the
scalar relation in the tensor product. None of these evaluation lemmas
requires finite generation of the coordinate algebra or of the test algebra.
