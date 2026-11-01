# Arithmetic pullback on smooth adelic rational functions

Author: Worker 2.

This internal construction uses an actual number-field ring isomorphism
`e : K ≃+* L`, independent field universes, and every natural matrix rank,
including zero. It restricts the actual continuous complex-linear ambient
arithmetic pullback to the existing smooth adelic function spaces. Complex
values are fixed.

The infinite-slice formula evaluates the original function on the transported
finite coordinate and the transported infinite argument. The actual
archimedean arithmetic smooth pullback therefore proves real smoothness of
every infinite slice. Continuous finite arithmetic substitution preserves
local constancy in every finite slice. A common open finite stabilizer pulls
back to its actual arithmetic preimage; the ambient fixed-submodule
correspondence proves that this subgroup fixes the entire pulled-back function.
Applying the inverse arithmetic pullback proves reflection of all three
conditions. The two intersections defining slice-wise smooth functions and
real-smooth functions with a common open finite stabilizer are consequently
preserved and reflected.

`smoothEquiv` and `finiteSmoothEquiv` restrict the actual ambient continuous
linear equivalence to these two existing subspaces. They retain the induced
compact-open topologies of the ambient continuous function realization.
Evaluation in both directions uses the actual field isomorphism and its
inverse. Identity, contravariant composition through a third independently
universed field, and equality of the inverse with inverse-field pullback are
proved for both equivalences. Both equivalences intertwine full right translation through the
actual arithmetic adelic group map. Pullback commutes with the existing
inclusion from the common-stabilizer space into the slice-wise smooth space.

`smoothCentralCharacterEquiv` further restricts pullback to the existing smooth
specified-character subspaces. The character transforms by the actual
`HeckeCharacter.comap e`; evaluation in both directions is the same arithmetic
function pullback. The restricted equivalence intertwines full right
translation on these actual specified-character subrepresentations.

Provenance is internal composition of the existing `Smooth` subspaces,
`AmbientArithmeticTransport`, and `ArchimedeanGLTransport`. Their explicit
intrinsic preservation and inverse laws justify each restricted construction.
No new original-literature identification is introduced. The topology here is
induced from the ambient compact-open continuous function topology; this file
does not assert continuity for a derivative topology. It asserts no
enveloping-center finiteness, growth, cuspidality, occurrence or classification
theorem, and does not identify the actual standard infinite compact subgroup
under a general field isomorphism.
