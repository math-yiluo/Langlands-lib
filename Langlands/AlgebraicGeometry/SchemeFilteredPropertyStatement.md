# Eventual smoothness and flatness of prescribed filtered-ring models

These propositions record the structural smoothness and flatness cases of
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed pp. 5-6, Theorem 3.4(2). Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
They specialize the relative morphism to the structure map of a prescribed
model over an original ring stage. Full descent for arbitrary morphisms
between two models remains a separate obligation.

For an arbitrary small filtered diagram `F` of commutative rings in universe
u and an actual colimit cocone `c` with witness `hc`, choose an original stage
`j₀` and a scheme `X` over its spectrum. Finite presentation means local
finite presentation, quasi-compactness and quasi-separatedness of `X.hom`.
`InitialRingModelPropertyDescent P` says that its actual pullback over the
specified cocone map has property `P` if and only if its actual pullback
along some original transition out of `j₀` has `P`. The existential index is
an object of `Under j₀`, so it includes the required actual arrow.

`InitialRingModelSmoothDescent` and `InitialRingModelFlatDescent` instantiate
this template with the existing scheme-morphism predicates `Smooth` and
`Flat`. The aggregate conjoins them; the witnessing arrows may differ.
There is no affineness or separatedness requirement on `X`, and original
transition maps may be noninjective. The base ring is an arbitrary
commutative ring, including the zero ring. Reverse implications follow by
base change. The intended forward proof uses structural model existence
and descent of an actual isomorphism between finitely presented models.
