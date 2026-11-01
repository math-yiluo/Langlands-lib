# Identity and composition of arbitrary-scheme etale sheaf images

This module constructs identity, equality and composition comparisons for
the actual direct and inverse images of small etale sheaves. It proves both
identity equations and associativity for direct image. For inverse image
it constructs the comparisons from the actual adjunctions and proves
their indicated unit and counit equations.

All schemes have universe `u`; every base morphism is arbitrary. Direct
image allows any category `A : Type uA` with morphisms in the independent
universe `vA`. Inverse image uses a commutative ring `R : Type u` and
`ModuleCat.{u} R`. There are no etaleness, finite-type, Noetherian,
finiteness, field, freeness or local-constancy hypotheses.

This is internal categorical infrastructure, derived from the existing
geometric fiber-product comparisons, their proved coherence equations,
Mathlib's functorial precomposition of sheaves, and uniqueness of adjoints.
It makes no new external-literature claim.

## Direct-image comparisons

For `f : Z ⟶ X`, `g : V ⟶ Z` and `h : W ⟶ V`, write `D_f` for
`EtaleDirectImage.directImage f A` and `P_f` for geometric pullback
of small etale objects.

`directImageId A X` identifies `D_(𝟙 X)` with the identity functor
using the actual fiber-product identity isomorphism. For an equality
`e : f = k`, `directImageCongr A e` uses the actual equality comparison
between the two fiber products. `directImageComp A f g` constructs

```text
D_g ⋙ D_f ≅ D_(g ≫ f)
```

from the actual single-to-iterated base-change isomorphism
`P_(g ≫ f) ≅ P_f ⋙ P_g`.

The three evaluation lemmas expose the inverse identity map, inverse
equality map and forward composition map. Each is the original sheaf's
map on the opposite of the corresponding geometric comparison. In
particular, writing `c(f,g,U)` for the geometric single-to-iterated
comparison, the composition component is `F.obj.map c(f,g,U).op`.

`directImageComp_id_target` and `directImageComp_id_source` prove
the two identity laws. They include the equality comparison for
`f ≫ 𝟙 X = f` and `𝟙 Z ≫ f = f`; no definitional identification
of the chosen fiber products is presumed.

`directImageComp_assoc` proves agreement of the two routes from
three successive direct images, including equality transport for
`(h ≫ g) ≫ f = h ≫ (g ≫ f)`.

For all three laws, extensionality first reduces the sheaf morphisms
to their components on a small etale test object. The evaluation
formulas and functoriality combine the section maps. Taking opposites
then reduces the equation to the corresponding proved geometric
fiber-product identity or associativity equation in
`EtaleTorsorPullbackCoherence`. The argument does not assume a thin
coefficient category or a thin site.

## Comparisons for the constructed inverse image

Write `L_f := EtaleInverseImage.inverseImage f R`.

`inverseImageIdentityAdjunction R X` transports the actual
adjunction `L_(𝟙 X) ⊣ D_(𝟙 X)` through `directImageId`, so its
right adjoint is the identity functor. `inverseImageId R X`
compares its left adjoint with the identity using
`Adjunction.leftAdjointUniq`. `inverseImageId_unit` proves that
this comparison, composed after the transported adjunction's
unit, is the identity on the source sheaf.

For `e : f = k`, `inverseImageCongr R e` first transports the
right adjoint of `L_f ⊣ D_f` through `directImageCongr`, then
uses uniqueness of left adjoints to compare `L_f` and `L_k`.

`inverseImageCompositeAdjunction R f g` composes the existing
adjunctions for `f` and `g`. It transports the resulting right
adjoint `D_g ⋙ D_f` through `directImageComp`. This gives

```text
L_f ⋙ L_g ⊣ D_(g ≫ f).
```

`inverseImageComp R f g` compares its left adjoint with the
constructed `L_(g ≫ f)` by uniqueness of left adjoints.
`inverseImageComp_unit` proves that the forward comparison
intertwines the composite and single-map adjunction units.
`inverseImageComp_counit` proves the corresponding counit equation.
These equations are the actual uniqueness-of-adjoints equations
from Mathlib, applied to the displayed constructed adjunctions.
No inverse-image comparison or desired compatibility is an input.

This module does not prove the full identity and associativity
coherence diagrams for inverse-image comparisons. Those diagrams,
arbitrary-map finite-limit preservation, comparison with torsor
coefficient systems, algebraic-closure base change, support and
derived comparisons, and Harris specialization remain separate
obligations.
