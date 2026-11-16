# Independent coefficient families for actual site points

This internal construction expands the existing Godement construction, using
Mathlib's actual site fiber/skyscraper adjunction. It is a categorical prerequisite
for studying compact supports of the analytic Godement terms. No acyclicity or
analytic comparison is assumed or established here.

For a family of points `points : I → J.Point`, `productSheaf` takes an independent
coefficient object `M i` at each point and forms the product of their actual
skyscraper sheaves. `productFunctor` makes this functorial, while `fiberFunctor`
collects the actual fibers. `homEquiv` and `adjunction` prove that these two
functors are adjoint by combining the individual skyscraper adjunctions with the
universal property of the product.

`godementZeroIso` identifies the existing `Godement.zeroFunctor` with their
composite. Its components are the canonical isomorphisms which evaluate a product
of functors, and naturality follows by projecting to each skyscraper.

`sectionsIso` evaluates the product of skyscrapers over an arbitrary site object
`X`: its coordinates are pairs consisting of a point `i` and an element of that
point's fiber over `X`. The proof uses preservation of products by the inclusion
of sheaves into presheaves and by evaluation. At a terminal object, every point
fiber is a singleton, and `globalSectionsIso` removes these singleton products.
These are formulas for actual sheaf sections; support and derived-functor
identifications remain separate obligations.

The provenance is the product universal property and the fiber/skyscraper
adjunction already used in `Langlands.Sheaf.Godement`, rather than a new theorem
attributed to the analytic literature. The point, index, site and coefficient
universes remain independent subject to the explicit product and colimit
existence hypotheses.
