# Finite-cover presentations of actual sheaf H¹ on compact spaces

Worker 368, internal construction. This construction uses only published
`AbelianSheafFlasque`, ordered `CechCochains`, and Mathlib's actual sheaf
epimorphism/local-surjectivity, compactness and cohomology exact-sequence
results. No external-source translation is asserted.

`FiniteLiftData φ q` records a finite index type, a full open cover, and a
zero-cochain lifting the restrictions of a global section `q` through a sheaf
morphism `φ`. If the underlying space is compact and `φ` is epi, local
surjectivity gives a lift near every point and compactness extracts a finite
subcover. No separation or Hausdorff assumption on the space is used.

`FiniteCocyclePresentation F x` records such a lift in the actual chosen
injective sequence of `F`, an ordered one-cocycle whose image is the
differential of the lift, and the equality of the actual connecting class
of `q` with `x : Sheaf.H F 1`. The existence theorem first lifts `x` to
degree-zero cohomology of the injective cokernel, using actual long exact
sequence exactness and vanishing of H¹ of an injective. It then takes a finite
cover of local lifts of the corresponding global section. Left exactness on
sections lifts the differential to `F`, and injectivity on sections and
`d² = 0` prove the cocycle condition.

The space `T : TopCat.{u}`, the abelian group sheaves and the finite cover's
index type all lie at an arbitrary universe `u`. The finite index is a subtype
of points selected by compactness; `FiniteLiftData.finite` records its
finiteness explicitly. `cover_top` is `⊤ ≤ iSup cover`. The cochains use the
ordered complex `Cech.C`: repeated indices are allowed, and the zero-cochain
component indexed by `σ : Fin 1 → index` lives on `Cech.inter cover σ`.
The construction restricts the pointwise local lifts to these intersections.

`injective_ι_section` records that the actual injective embedding is injective
on sections of every open set. The existence proof uses this to deduce that
the lifted cochain is closed, by mapping its differential into the injective
sheaf and applying `d² = 0`. `primitive_eq` uses the exact chosen embedding
`Injective.ι F`; `value_eq` uses Mathlib's actual `Sheaf.H.δ` for
`AbelianSheafFlasque.injectiveSc_shortExact F` and the actual degree-zero
equivalence with global sections. No comparison with another cohomology
theory is assumed.

The cover may depend on the class. This module does not construct a map
from its cocycles into cohomology, assert surjectivity on any fixed cover, or
provide a line-bundle classification or a Picard representability proof.
