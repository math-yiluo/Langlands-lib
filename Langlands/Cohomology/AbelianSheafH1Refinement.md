# Refinements and finite-cover coverage of actual abelian sheaf H¹

Worker 368, internal derivation from the published finite-cover comparison in
`AbelianSheafCechH1`, actual finite cocycle presentations in
`AbelianSheafH1FiniteCocycles`, and ordered refinement in `CechRefine`.
No external-source translation is asserted. The coefficients are actual
abelian sheaves and the target is Mathlib's actual Ext-defined `Sheaf.H`.

The topological space `T : TopCat.{u}` and coefficient groups have arbitrary
universe `u`. Refinement index types have independent universes `w` and `w'`.
For open families `U` and `U'`, an index map `β` and inclusions
`hβ : ∀ j, U' j ≤ U (β j)` specify a refinement. No full-cover or finite-index
hypothesis is needed for the initial constructions.

`refine_globalCochain` proves that restricting a global section and then
refining gives its zero-cochain on the refined family. Functorial composition
of restrictions proves the identity. `refineCocycles` restricts ordered
one-cocycles, using commutation with the differential. The same commutation
sends every coboundary to a coboundary, so `refineHom` induces an additive
homomorphism between the quotients `CechH1`. `refineHom_mk` evaluates it on
any cocycle class. Ordered tuples, including repeated indices, are retained.

For any short complex of abelian sheaves, `refineRepresentative` restricts a
representative's primitive and retains its global quotient section. Commutation
of refinement with the differential and with sheaf maps proves the primitive
equation. Commutation with the global zero-cochain proves the quotient equation.
For a short exact complex, `refineRepresentative_value` states that the actual
connecting value is unchanged; both sides apply the same actual `Sheaf.H.δ`
to the same global quotient section under the degree-zero equivalence.

If both index types are finite, both families cover the whole space
(`⊤ ≤ iSup U`, `⊤ ≤ iSup U'`), and the middle sheaf is flasque,
`quotientClassHom_refine` proves that refinement preserves the comparison
class. The proof reduces a quotient class to a cocycle, chooses a representative
on the original cover, refines it and evaluates both comparison maps with
these representatives. The preceding identity equates the values. Specializing
to the chosen injective sequence gives `comparisonHom_refine` for every
actual abelian sheaf. `refineHom_injective` follows by applying the injective
comparison on the original finite full cover to an equality after refinement.
No compactness is used for these refinement results.

`presentationRepresentative` converts the published finite cocycle presentation
of a class `x : Sheaf.H F 1` into a representative in the actual chosen
injective sequence. The presentation's primitive equation is reversed and
its componentwise lifting equation becomes the quotient equation. Its
`value_eq` is exactly `presentationRepresentative_value`.

Finally, `exists_comparisonHom_eq` proves that, on a compact topological space,
for every `x : Sheaf.H F 1` there are an index type `ι : Type u`, a `Finite ι`
instance, a full cover `U`, and `z : CechH1 F.1 U` with
`comparisonHom F U hcov z = x`. The proof uses the published existence of a
finite cocycle presentation, takes the class of its closed cocycle, and
evaluates the comparison with its supplied representative. The cover may
depend on the class. No separation assumption on the space is used.

This module does not assert fixed-cover surjectivity, sheaf-morphism
naturality, a line-bundle classification, or final Picard representability.
