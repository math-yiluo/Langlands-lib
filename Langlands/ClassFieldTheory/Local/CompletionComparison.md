# Universal property of the open finite quotient completion

Worker 1556 develops this internal topological comparison for the local
reciprocity completion proof. It uses Worker 21's published closure of the
actual diagonal image in the product of open finite quotients. No source
quotient is added without its original-topology openness certificate.

For a compact Hausdorff totally disconnected group H, open normal subgroups
separate elements, and compactness makes the canonical dense completion map
surjective. Thus etaEquiv identifies H continuously with its actual completion.
The completion map induced by a continuous homomorphism f, followed by the
inverse of etaEquiv, gives lift f. It agrees with f on the canonical source.
Density gives uniqueness, and density of f makes this lift surjective by
compactness and Hausdorffness.

The final conditional criterion assumes that every actual open finite quotient
of the source descends continuously through f to H. The descended maps agree
with the completion coordinates on the dense canonical image and therefore
everywhere. Consequently they separate completion points, proving injectivity
of the lift. A continuous bijection from the compact completion to Hausdorff H
has continuous inverse. Density also proves uniqueness of the resulting
continuous group equivalence.

This is a derived elementary topology argument using Mathlib's open normal
subgroup theorem, quotient groups, compactness and density. It uses no external
literature beyond the construction provenance recorded in Completion.md, and
asserts no arithmetic norm-existence theorem or local reciprocity theorem.

## Declarations and scope

All declarations are in `Langlands.LocalClassField.ContinuousProfinite`, with
independent universes `u` and `v`. The source G is any topological group; the
main target H is any compact Hausdorff totally disconnected topological group.
`map_eta` and `hom_ext` give naturality and determination on the dense image.
`eta_injective`, `eta_surjective` and `etaEquiv` establish the canonical
comparison for H. `lift` is the actual continuous homomorphism constructed
from `map f` and the inverse of `etaEquiv`; `lift_eta` is its extension law.
`lift_surjective` retains `DenseRange f` explicitly.

The exact descent premise in
`lift_injective_of_finite_quotient_descent` and
`existsUnique_equiv_of_finite_quotient_descent` is
`∀ N : OpenFiniteQuotient G, ∃ q : H →ₜ* N.Quotient,
q.comp f = N.projection`. The last theorem concludes unique existence of
`e : Completion G ≃ₜ* H` with `e (eta G g) = f g` for every g.
It does not assert injectivity of f: separation of elements of G by its open
finite quotients is a separate obligation. In particular, deriving descent
from norm groups, and proving injectivity of local reciprocity on field units,
remain with the arithmetic application.

Worker 21 remains the author of the imported completion construction. This
pair uses that published construction by Lean name. The new proof argument
and definitions here are by Worker 1556; agreement on division of work with
Worker 1607 contributes no mathematical input to this pair.
