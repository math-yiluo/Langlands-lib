# Covering coactions on Hom modules

This internal construction gives a covering coaction on Hom over the base
object ring. The source of Hom is a module on the covering relation, finite
presented over the base object ring; its target is an arbitrary base
coaction. The construction is derived from the actual Hom coaction and
the source-cartesian tensor comparison.

More precisely, the object and relation rings are commutative rings
`B, C, D, P` in an arbitrary universe `u`. The source algebra structures
and the equivalence `e : P ≃ₐ[D] D ⊗[B] C` are compatible with the
base algebra action, and the two target maps satisfy
`(cartesianBaseMap e).comp t = td.comp (algebraMap B D)`.
Both target maps carry the published ring étale equivalence relation
structure. The source and target modules have an independent universe
`v`, and the source is finitely presented over `B`. No flatness of
`B → D` is assumed. Flatness of `B → C`, needed for Hom base change,
follows from the base relation's source étaleness.

The covering ring acts by multiplication in the source:
`(d • f)(y) = f(d • y)`. Commutativity gives the module laws and linearity
of `f` identifies the restricted action with the existing base action
on Hom. The module and scalar-tower instances are local to this file;
callers can install `homSourceModule` and `homSourceTower` locally when
using `coveringHom`.

The tensor evaluation identity balances the covering relation ring action
between the Hom factor and its source. Its proof uses cartesian tensor
generators for both factors and tensor generators for the relation ring.
On these generators the identity is scalar associativity and the displayed
source action.

To check target semilinearity of the lifted Hom coaction, extend Hom to
the base relation ring and test equality on coaction values of the source;
these span by the published coaction spanning lemma. The evaluation formula
for the actual Hom coaction and the balanced tensor evaluation identity
reduce the assertion to target semilinearity of the covering source
coaction. The source-cartesian lifting constructor then proves the counit
and cocycle laws. Pushing this covering Hom coaction forward gives exactly
the original base Hom coaction.

This pair constructs the covering coaction. Vanishing under an effective
faithfully flat covering presentation, restrictions to ideal powers, and
the support induction for the host acyclicity theorem are further steps.
