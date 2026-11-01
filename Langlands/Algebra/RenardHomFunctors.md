# Renard's pseudo-forgetful functor and right induction

This internal arbitrary-ring additive specialization supports Renard, French
edition dated 9 July 2026, I.2.3, printed pages 16–18 / PDF22–24, especially
(I.2.3.2) and the definition of I. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The conventions at printed pages 5–7 / PDF11–13 allow actions without a unit law.
Renard's motivating setting uses complex algebras and nondegenerate bimodules;
the present definitions retain only the original additive groups and actions.

For `pseudoF`, B carries exactly `NonUnitalModule.regular B` on the left and the
supplied original right A-action, with the supplied commutation witness.
`pseudoAction` is the published named `sourceAction` on the actual
`NonUnitalModuleHom B B M`. Thus `(a • φ)(b) = φ(op a • b)`, which is the
source's `φ(b a)` notation. `pseudoPart` is the A-nondegenerate part, and membership
is the existence of an actual idempotent e of A with φ(op e • b) = φ(b) for all b.

For `I`, B has its supplied original left A-action and exactly
`NonUnitalModule.rightRegular B` on the right, with the supplied commutation
witness. `inductionAction` is the published source-precomposition action on
`NonUnitalModuleHom A B M`. Its formula is `(b • φ)(b') = φ(b' * b)`.
`inductionPart` takes the B-nondegenerate part. Membership is exactly fixation
by an actual idempotent e of B, expressed as φ(b' * e) = φ(b') for all b'.

Both functors are literally the corresponding `restrictedFunctor` of
`NondegenerateHomFunctor`: include the nondegenerate input into all original
modules, apply the ambient fixed-source Hom functor, then apply the published
nondegenerate-part functor. Their carrier universes are exactly the maximum of
the universe of B and that of the variable module. Both ring universes and the
variable carrier universe are independent. No target right action is needed.
Only idempotentedness of the output ring enters the direct definition.

The complete composite, bundled object, carrier, inherited additive group and
original action are exposed, together with the inherited scalar/subtype
formulas. `pseudoMap` and `inductionMap` reuse `partMap` and allow independent
input/output carrier universes. The maps are exactly restrictions of original
postcomposition, with whole underlying additive-map and subtype-value
equalities and evaluation formulas. Their additivity follows from the actual
published additive inclusion and part functor and the constructed ambient
functor. The two natural inclusions are precisely the restricted whiskered
inclusion of the part. Each component is the actual submodule subtype map,
and naturality is equality of whole original linear maps.

`pseudoFOfNondegenerate` and `IOfNondegenerate` accept the published
`IsNondegenerateBimodule` for exactly those selected actions and the same
commutation witness. They return the respective direct construction. No
nondegeneracy is inferred from a ring homomorphism. These adapters expose the
source's stronger assumptions without adding unused hypotheses to the direct
construction.

The supplementary registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF1–2 and PDF18–19: its printed-page-299 correction agrees with
the implemented postcomposition in the covariant variable. Its printed-page-20
adjunction correction is reflected in the 2026 source, but no adjunction is
asserted here.

Coefficient-linear and unitization comparisons, completion and regular-Hom
equivalences beyond these direct object formulas, equality of the two Hom
parts, scalar restriction, tensor-Hom equivalences, categorical adjunctions,
exactness and the tensor-based F/P constructions remain separate successors.
This pair does not assert full coverage of I.2.3 or the book.
