# Derived sections of compatible coefficients over varying schemes

This internal construction lifts the actual compatible-coefficient category of
`EtaleCohomologyDiagramFunctor` to diagrams in the bounded-below derived category.
Its geometric maps are the localized section maps of
`EtaleDerivedPlusPullback`; their identity and composition laws are proved in
`EtaleDerivedPlusPullbackFunctoriality`. No derived transition map or derived
compatibility equation is assumed as input.

Fix a commutative ring `R : Type u`, schemes in `Scheme.{u}`, and an indexing
category `J : Type v` with morphisms in universe `w`. The actual scheme diagram
is `S : J ⥤ Scheme.{u}ᵒᵖ`, every underlying scheme map is etale, and an object
`D : CoefficientDiagram R S` supplies actual small-etale module sheaves and
restriction-compatible coefficient morphisms. Choose derived localizations of
the sheaf categories in one universe `wS`, independently of the localization
universe `wT` for modules. The indexing universes are independent of these.
The preliminary three-scheme lemmas allow independent sheaf localization
universes at their three vertices.

`derivedSectionsMap_congr` transports derived pullback along an equality of
scheme maps. Its proof eliminates the equality and simplifies identities.
`derivedSectionsMapWithCoefficients_comp` identifies successive derived
pullbacks with the composite pullback and the coefficient map obtained by
inverse restriction comparison, restriction of the first coefficient map,
and the second coefficient map. Its proof uses the derived composition law,
cancels the restriction comparison, and applies coefficient naturality.
`diagramDerivedSectionsMap_id` and `diagramDerivedSectionsMap_comp` transport
the same laws through the scheme diagram's identity and composition equations.
All these equations hold in D⁺ itself.

`CoefficientDiagram.derivedSections D` has object `RΓ(X_i,D.obj i)` at vertex
`i`, where `X_i = (S.obj i).unop`. For `a : i ⟶ j`, its arrow is geometric
derived pullback along `(S.map a).unop : X_j ⟶ X_i`, followed by derived
sections of the actual coefficient morphism `D.map a`. The functor's identity
law follows from the coefficient identity and the transported derived identity
law. Composition follows from the transported derived composition law, the
coefficient composition equation, and naturality in the coefficient sheaf.
The transition coefficient maps need not be isomorphisms.

`derivedSectionsMap α` acts at vertex `i` by derived sections of `α.app i`.
Its naturality combines the coefficient morphism's compatibility equation
with naturality of geometric derived pullback. Pointwise functoriality then
constructs `derivedSectionsFunctor`, from compatible coefficients to actual
`J`-diagrams in D⁺ of modules.

For `q : ℕ`, `derivedSectionsHomologyIso D q` identifies cohomology of this
derived diagram with the previously published ordinary diagram `D.cohomology q`.
Its components are the existing canonical `homologyNatIso` components; their
naturality along every diagram arrow is exactly the proved recovery equation
for derived pullback with a coefficient morphism.
`derivedSectionsHomologyFunctorIso q` makes this identification natural also
in coefficient diagrams, using the coefficient naturality of `homologyNatIso`
at each vertex. Composing with the published ordinary degree-zero comparison
gives `derivedSectionsZeroIso` and `derivedSectionsZeroFunctorIso`, identifying
degree-zero derived cohomology with ordinary sections in both variables.

This is derived internal infrastructure, not a new named theorem from Harris
or Berkovich. It uses ordinary global sections over a fixed scalar ring.
It constructs no compact supports, trace maps, scalar change, inverse limits
or Shimura tower. Applying it to Harris still requires actual geometric
spaces, etale transition maps and compatible coefficient sheaves.
