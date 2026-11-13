# Explicit Hecke Hom comparison for smooth induction: proof

`Langlands.Hecke.Homomorphism.closedInductionHom` proves the exact published
`ClosedInductionHomStatement.{uG, v}`. The group universe and the coefficient
carrier universe remain independent. The proof constructs a natural isomorphism
between `inducedHeckeFunctor` and `homInductionHeckeFunctor` and proves all four
prescribed formula clauses. It adds no hypotheses to the statement and does not
use a supplied equivalence between smooth representations and Hecke modules.
Local compactness of the closed subgroup is obtained from its closedness at the
final theorem.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, III.2.5 Remark, equations (III.2.5.1)–(III.2.5.5), printed
pp.74–75 / PDF pp.80–81. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The helpers in this module are internal constructions and consequences supporting
this proof, rather than separately attributed assertions of the source.

The proof uses the original carrier
`NonUnitalModuleHom (HeckeAlgebra μH) (HeckeAlgebra μG) W`, with the published
integrated restricted left regular action on its source. `closedHom` names that
carrier, and `homInductionRaw` exposes the module map beneath a nondegenerate
Hom vector. `closedHom_map_complex` and `closedHom_map_group` prove automatic
complex linearity and equivariance for the original action of `H`. For either
identity one chooses an idempotent fixing the input test function. Linearity for
the subgroup Hecke action then transfers the complex scalar identity, or the
left-translation identity for the integrated action, to its image in `W`.

`closedForwardLinear` implements the prescribed formula
`q_f(T) = (T · f)(1)`. Evaluation at 1 is complex linear. Its covariance under
restricted left translation follows from `integratedAction_leftTranslate` and
the covariance of the actual induced function. Hence it is an intertwiner, and
`integratedAction_intertwiner` makes `closedForwardRaw` linear for `H(H)`.
Associativity of the actual integrated Hecke action gives
`q_f(T * a) = q_(a · f)(T)`. A compact-open normalized indicator fixing `f`
therefore fixes `q_f` under the residual precomposition action. This proves
membership in the actual nondegenerate Hom part and supplies the morphism
`closedForwardHom`.

`closedForward_translate` identifies `q_f(l(g)a)` with `(a · f)(g)`. A common
normalized indicator fixing two smooth functions then shows that equality of
their forward images implies pointwise equality. This proves
`closedForward_injective` on the original smooth-function space.

For the inverse, `homInduction_exists_localUnit` first replaces an idempotent
fixing an original Hom vector by a compact-open normalized indicator. The
finite-family local-unit theorem supplies `e_K` with `e_K * e = e`; associativity
and the fixing identity for `e` give `q(T * e_K) = q(T)` for every `T`.
For any compact-open subgroup, `closedInverseAt` constructs the actual function
`g ↦ q(l(g)e_K)`. Its `H`-covariance follows from `closedHom_map_group`. Its single
uniform right stabilizer is `K`, because `e_K` is invariant under left
translation by `K`. Thus this is a vector of the published smooth induction,
not merely a pointwise locally constant function.

The published `integratedAction_leftTests` theorem from
`CompactInductionComparisonLaws` identifies the integrated left regular
representation with actual convolution by applying scalar point evaluations
and `integratedAction_dual`. In `closedForward_inverseAt`, arbitrary algebraic
complex-linear functionals on `W` compare the forward image of the constructed
inverse function with `q(T * e_K)`. The two scalar integrals agree pointwise,
and the regular convolution identity finishes the calculation. Algebraic dual
separation then gives the vector identity. A fixing `e_K` makes this identity
`q_f(T) = q(T)`, proving `closedForward_surjective`.

`closedInverse` chooses a preimage from that surjectivity proof.
`closedForward_inverse` and injectivity give both inverse identities.
`closedInverse_formula` compares the chosen preimage with `closedInverseAt`
for every fixing compact-open subgroup. It therefore proves the required
inverse formula independently of the choice of local unit. Additivity and
Hecke linearity of the inverse follow by applying the injective forward
morphism, yielding `closedInverseHom` and `closedComponentIso`.

Naturality is proved directly: postcomposition by an intertwiner commutes with
the integrated action and with evaluation. The Hom induction functor acts by
that same postcomposition. `closedComponent_naturality` supplies the naturality
square, and `closedComparisonIso` bundles the components into a natural
isomorphism. Finally, `leftModule_translated_localUnit` proves the prescribed
restricted-action identity `(l(h)e_U) · T = l(h)T` whenever `e_U · T = T`, by the
published left-translation identity for the integrated restricted regular action.
The final theorem packages this identity with the forward, local-unit and inverse
formulas for `closedComparisonIso`.

The proof uses `integratedAction_leftTests` directly; the former
`integrated_leftTests` alias has been removed.
