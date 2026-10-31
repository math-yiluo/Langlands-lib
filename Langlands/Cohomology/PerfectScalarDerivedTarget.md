# Perfect-source Hom adjunction with arbitrary derived targets

This internal construction extends the published
`kProjectiveDerivedAdjunctionHomEquiv` and `perfectScalarDerivedHomEquiv`
from `PerfectScalarAdjunctionProof`. Their targets have the form `Q.obj L`;
the new equivalences allow any object of the actual derived category.

For an additive adjunction `F ⊣ G` between abelian categories, assume that `G`
preserves finite limits and finite colimits, and that both `K` and the termwise
image `F(K)` are K-projective. For every `Y : DerivedCategory D`,
`kProjectiveDerivedTargetHomEquiv` identifies maps `Q(F(K)) → Y` with maps
`Q(K) → G.mapDerivedCategory.obj Y`. Its forward function is definitionally the
published derived unit followed by `G.mapDerivedCategory.map`.

The proof of bijectivity chooses a complex representative `L` and an isomorphism
`Q.obj L ≅ Y` using essential surjectivity of the localization functor `Q`. It
transports the published equivalence for `L` through this isomorphism and its
image under the exact right adjoint. The published unit formula and functoriality
identify the resulting function with the canonical one. `Equiv.ofBijective`
therefore gives an equivalence whose forward function does not depend on the
chosen representative. The target naturality lemma follows from functoriality.
The inverse characterization says that its value is the unique morphism with
the specified unit image. The `Q_obj` lemma recovers the published equivalence
when the target is presented by a complex.

`ModuleComplex.perfectScalarDerivedTargetHomEquiv` specializes this construction
to extension and restriction of scalars for any commutative ring homomorphism.
The source is strictly perfect; the published K-projectivity helpers apply both
before and after ordinary termwise scalar extension. The module supplies the
same forward formula, target naturality, inverse characterization, and
compatibility with `perfectScalarDerivedHomEquiv`.

The generic source and target category, morphism, and localization universes
are independent. The scalar construction allows arbitrary ring universe `u`
and independent localization universes. It requires no flatness of the ring map,
no exactness of the generic left adjoint, and no injective resolutions. This
adapter alone proves no geometric base-change, section-lifting, perfectness,
or relative cube assertion. Its provenance is the published adjunction proof
and Mathlib's essential-surjectivity API; no new external source is used.
