# Geometric action diagrams with arbitrary level morphisms

This internal construction turns an actual geometric coefficient diagram on a
product index category into action-valued derived-section, ordinary-cohomology
and section diagrams. It derives the actions and equivariance from the existing
geometric pullback constructions and the product-index functor laws.

The inputs are a commutative ring `R : Type u`, a category `J : Type v` with
morphisms in `Type w`, a group `G : Type t`, and a scheme diagram
`S : (J × SingleObj G) ⥤ Scheme.{u}ᵒᵖ`. A
`EtaleGeometricDiagram.CoefficientDiagram R S` supplies actual small-etale
`R`-module sheaves at the vertices and coherent geometric inverse-image
coefficient maps along the arrows. No etaleness condition is imposed on the
scheme maps, and coefficient transition maps need not be isomorphisms.
The cohomological declarations retain a common sheaf-localization universe `wS`
at every product-index vertex and an independent module-localization universe
`wR`. Ordinary degrees `q` are natural numbers.

`actionDiagramFunctor` is a general categorical construction. It curries a
functor on `J × SingleObj G` and postcomposes with the inverse of Mathlib's
equivalence between `G`-actions and functors from `SingleObj G`. This helper
needs only a monoid. The geometric constructions specialize it to a group.

For supplied coefficients `D`, `derivedAction D`, `cohomologyAction D q` and
`sectionsAction D` are functors from `J` to the categories of `G`-actions on
bounded-below derived `R`-modules, ordinary `R`-modules and section modules,
respectively. The corresponding `*ActionFunctor` declarations are functors on
the category of compatible geometric coefficients.

At level `i`, the underlying objects are the actual derived sections, degree-`q`
right-derived global sections and actual global sections of
`D.obj (i, SingleObj.star G)`. A group element `g` acts along the product arrow
`𝟙 i ×ₘ g`. The level map for `a : i ⟶ j` acts along
`a ×ₘ 𝟙 (SingleObj.star G)`. The `*_obj_ρ` and `*_map_hom` theorems identify these
maps with the existing geometric pullback with coefficients. For derived
sections this is `sheafDerivedPullbackWithCoefficients`; for ordinary cohomology
and sections these are `cohomologyPullbackWithCoefficients` and
`sectionsPullbackWithCoefficients`.

The action laws follow from the functor laws on `SingleObj G`; its composition
convention gives `ρ (g * h) = ρ h ≫ ρ g`. The commuting product-index arrows
give equivariance of every level map. `derivedAction_map_comm` records this
equation explicitly. The coefficient-functor component theorems identify each
underlying map with the actual vertex cohomological functor applied to
`α.app (i, SingleObj.star G)`.

`derivedActionHomologyIso D q` identifies homology of the derived action diagram
with the ordinary cohomology action diagram. Its components are the existing
canonical `EtaleDerivedSectionsPlus.homologyNatIso` maps.
`derivedActionZeroIso D` identifies degree-zero homology with actual sections
with components `EtaleDerivedSectionsPlus.homologyZeroIso`.
Both are isomorphisms of action-valued level diagrams and have corresponding
`*FunctorIso` declarations natural in all compatible coefficient morphisms.
The proof constructs `Action.mkIso` from the existing canonical comparisons;
their naturality along `𝟙 i ×ₘ g` proves equivariance and their naturality along
`a ×ₘ 𝟙 star` proves compatibility with every level map. Naturality of the
canonical vertex comparisons proves the coefficient-functor equations.
`cohomologyActionZeroFunctorIso` is the existing ordinary degree-zero comparison
postcomposed with `actionDiagramFunctor`.

The provenance is internal categorical assembly from
`EtaleGeometricCoefficientDiagram`, Mathlib currying and Mathlib's category of
actions. The input contains actual sheaves and inverse-image coefficient maps;
cohomology objects, actions and recovery comparisons are constructed from them.
This pair does not construct an arithmetic scheme tower or an action on one
from separate data. Topological smoothness, support conditions, tower limits,
Galois continuity, arithmetic coefficient systems and the Harris specialization
remain separate obligations.
