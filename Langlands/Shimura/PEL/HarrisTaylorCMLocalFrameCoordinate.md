# Local coordinates of actual Harris frames

This internal unit evaluates an actual compatible adelic frame at a specified
finite place of the rationals. It uses the original Harris group and the actual
rational Tate action. It derives its content from the imported actual frame
constructions and the published finite-order/local-smallness reduction.

`localFrameCoordinate` takes an actual full rational Tate section, applies the
inverse of a chosen actual Weil-compatible frame, and evaluates the resulting
finite-adelic source coefficients at the given finite completion. Its target
is the completion tensor the original rational algebra. This construction
retains the chosen frame; it does not assert faithfulness of one coordinate
or identify this coordinate space with the actual prime-adic Tate module.

`localFrameCoordinate_frame_isogeny` rewrites the actual frame equation in
these coordinates. The rational self-isogeny acts by right multiplication by
the evaluated underlying original Harris element. To prove this, evaluate the
frame equality on an arbitrary source vector, use the original scalar-extension
equivalence's right-multiplication formula, then substitute the inverse frame
of the Tate section. Applying coefficient evaluation preserves multiplication.

`localFrameCoordinate_fixed_of_local_identity` assumes that the same original
element is the identity under the actual local points map. Projecting its
underlying algebra unit and applying the preceding formula shows that every
local coordinate is fixed by the rational self-isogeny.

`exists_localFrameCoordinate_fixed_of_levelIso_fixed` assumes an actual fixed
level orbit, the original level's smallness at the selected place, and finite
order of the actual rational endomorphism. The imported finite-order reduction
extracts an actual compatible frame and original subgroup element whose local
image is one. The preceding theorem then gives the fixed-coordinate conclusion.

Finite order remains an explicit premise. Deriving it, comparing these local
coordinates with the actual prime-adic Tate action, and applying one-prime
faithfulness remain obligations of the exact rigidity theorem. This unit does
not prove that theorem and makes no external source attribution.
