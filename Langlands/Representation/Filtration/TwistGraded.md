# Graded quotients of character-twisted filtrations

`Langlands.RepFunctorFiltration.twistGradedIso s χ i` is a natural
isomorphism from `(s.twist χ).graded i` to `(s.graded i) ⋙ χ.twistFunctor`.
Here `s` is the published finite filtration by actual subfunctors, and `χ`
is the published smooth unit-valued scalar character. The construction retains
the original length, every filtration step and its index.

The more general `Langlands.RepSubfunctor.twistQuotientIso S T χ` compares
`(S.twist χ).quotientFunctor (T.twist χ)` with
`(S.quotientFunctor T) ⋙ χ.twistFunctor` for arbitrary actual subfunctors
`S` and `T`. No containment assumption is needed: the quotient interface
already pulls the lower submodule back to the upper submodule.

For each object `X`, twisting preserves the underlying upper submodule and
the pulled-back lower submodule. Both quotient modules are therefore the same
module. On both sides the action is

\[
 g\,[v]=[\chi(g)\rho(g)v]=\chi(g)[\rho(g)v].
\]

The component representation equivalence uses the identity linear equivalence
on this actual quotient module; intertwining follows by unfolding the published
quotient and scalar-twist actions. `Rep.mkIso` packages it as an isomorphism of
representations, including both inverse laws. `NatIso.ofComponents` gives the
natural isomorphism: the underlying descended functor maps agree, since twisting
leaves all original linear maps unchanged. The code verifies this naturality
by extensionality on quotient elements.

The forward and inverse `twistQuotientIso_*_app_apply` lemmas state that the
component maps fix every underlying quotient element. The two
`twistQuotientIso_*_projection` lemmas give the representative formula in both
directions: the class of `v` maps to the class of that same `v`. The filtration
comparison specializes this construction to `s.step i.castSucc` and
`s.step i.succ`; its forward and inverse application lemmas likewise fix every
quotient element.

The coefficient ring, group, representation carrier, source-category object
and source-category morphism universes remain independent. The ring is any
commutative ring. No topology on the ring, finite dimension, finite composition
length, smoothness of the representation objects or splitting is required.
Zero filtration length, repeated steps and zero quotient modules are retained.
The character has an open kernel as required by the existing twist-functor
interface; the comparison itself uses its algebraic scalar action.

This is an internal construction from `Filtration.Definitions`,
`Filtration.Transport`, `Twist.SubquotientDefinitions` and the scalar twist
functor in `Induction.Definitions`. It asserts no separate theorem from the
literature. It supplies only the natural graded comparison for scalar twists;
normalized Jacquet comparisons, geometric-lemma filtrations, multiplicity
identities and irreducible-head assertions require further work.
