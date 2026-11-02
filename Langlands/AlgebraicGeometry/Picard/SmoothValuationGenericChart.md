# Generic trivializations on total principal neighbourhoods

This internal construction chooses a total principal neighbourhood and an
actual sheaf trivialization over its generic part. Let `R` be an arbitrary
valuation domain, let `A` be a smooth `R`-algebra, let `K` be any supplied
fraction field of `R`, and let `P` be any prime ideal of `A`. Write
`B = A ⊗[R] K`. There is no Noetherian, rank-one valuation or discreteness
hypothesis; fields are included.

First, `invertible_moduleSpecΓ_of_lineBundle` identifies the actual
sections of any line bundle on `Spec B`, with their canonical `B`-module
structure, as an invertible `B`-module. The imported affine-sections
theorem gives invertibility over `Γ(Spec B, ⊤)`. The canonical map from
`B` to that ring is bijective. Surjectivity makes tensor products over
the two coefficient rings agree. Restricting the duality equivalence
and composing with the inverse coefficient equivalence therefore proves
invertibility over `B` itself. This part holds for every commutative
ring, independently of the valuation assumptions.

The localization of `B` at the images of the elements outside `P` has
trivial module Picard group. The proof expresses that localization as
`A_P ⊗[A] B`, using localization under scalar extension, and identifies
it with `A_P ⊗[R] K` by tensor associativity. The latter is a localization
of the coherent regular local ring `A_P`, so the imported localized
Picard vanishing theorem applies. Picard vanishing transports through
the resulting ring equivalences.

An invertible module over `B` is finitely presented. Its localization at
that multiplicative set is free of rank one. Mathlib's finite
presentation lifting theorem spreads the resulting linear equivalence
to inversion of one element of the multiplicative set. That element is
the image of an actual `a` outside `P`. This proves
`exists_generic_principal_module_trivialization`.

For an actual Library line bundle `D` on `Spec B`, apply that lemma to
its actual sections. The associated-sheaf counit recovers the original
quasi-coherent sheaf `D.obj`. Pulling back its inverse along the
localization map, using `tildePullbackAlgebraIso`, and sheafifying the
localized module basis gives an actual isomorphism from the pullback of
`D.obj` to the structure sheaf on `Spec (B[1/a])`. The definition
`genericPrincipalLineBundleTrivialization` chooses both the total
function `a` outside `P` and this actual sheaf isomorphism.

The provenance is the internal derivation above from the imported
smooth valuation regularity, localized Picard vanishing, affine-sections
and associated-sheaf constructions, together with Mathlib's tensor,
localization and finite presentation interfaces. This construction gives
local generic trivializations on total principal neighbourhoods. It
asserts no compatibility on intersections or global extension.
