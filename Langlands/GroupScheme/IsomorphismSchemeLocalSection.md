# Local orbit sections over the original base

This internal construction is derived from the actual scheme pullback
adjunction, its product comparisons, and the existing all-test Isom
action and parameter-section interfaces.

Suppose an Isom representative is pulled back along `b : U ⟶ S`.
A supplied section family over `U`, with parameter `Q`, gives a family
over `S` by composing its image under `Over.map b` with the pullback
adjunction's counit. Its local-base parameter is retained by the
structure map from the same `Q` to `U`, viewed over `S`.

The implementation constructs two canonical isomorphisms. The actual
pullback of any relative parameter, viewed over `S`, is its product
with `U` in `Over S`. The product of a pulled-back factor with `Q`,
viewed over `S`, is the product of the original factor with the same
`Q` viewed over `S`. The latter is the standard iterated-pullback
isomorphism; the projection identities are proved explicitly.

Under these comparisons, the orbit morphism over `U` is exactly the
parameter-preserving orbit-family morphism over `S`. The first
projection equality uses compatibility of the Isom action with
base change under the pullback adjunction. The second is the fact
that every morphism over `U` retains its structure map.

If the orbit decomposition is bijective on every scheme test over
`U`, the orbit morphism is an isomorphism by the existing normalized
section constructor. The two canonical comparisons therefore make
the parameter-preserving orbit morphism over `S` an isomorphism.
This yields its full all-test bijection, including the local-base
coordinate, as required by parameter-section descent.

The family and its decomposition are explicit inputs. No cover
condition, geometric condition on `Q`, pinned classification or
independent quotient-existence theorem is asserted here. All bases
and relative tests remain arbitrary.
