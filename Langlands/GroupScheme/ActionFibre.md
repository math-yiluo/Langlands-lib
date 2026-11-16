# Fibres of invariant scheme morphisms

Worker 217.

This internal construction concerns arbitrary schemes over a base `S`.
Let `q : X → Q` be a relative morphism and `s : S → Q` a section.
`ActionFibre.parameter q s` is the actual scheme pullback of their underlying
morphisms, with its projection to `S`. The morphism `projection` maps this fibre to
`X`, and `projection_comp` proves its required class equation. Morphisms into the
fibre are determined by their ambient components (`hom_ext`).
`pointLift` constructs the actual pullback lift of every ambient point whose
class is the restriction of `s`, and `pointLift_projection` retains that point exactly.

Flatness, surjectivity and quasi-compactness of the underlying morphism `q`
each pass to the fibre's structure morphism by base change.

Suppose an actual group scheme `A` acts on `X` through `ModObj`, and on every
relative test the class morphism is invariant. `actionHom` lifts the ambient
action to one actual morphism on the fibre. Its projection evaluates to the
ambient action on every test (`actionHom_eval`). The construction `modObj`
proves the unit and multiplication laws by this equation and `hom_ext`;
`smul_projection` states equivariance of the fibre projection.

Finally, suppose that for every test and each pair of points of `X` with the
same class, there is a unique point of `A` carrying the first to the second.
`leftSMul_isIso` applies this condition to projected fibre points, lifts the
resulting equality by `hom_ext`, and uses the categorical all-test shear
criterion. Thus the fibre is an actual torsor when the three supplied
covering properties of `q` also hold.

All statements are conditional on the specified action, invariance and
unique-difference hypotheses. No quotient existence or representability is
asserted. The proof uses the imported Library's action construction and
Mathlib's scheme pullbacks and categorical shear criterion. It generalizes
the pullback and action method of `Dynamic.FlagQuotientFiber`, whose ambient
scheme is a group and whose action is derived from an exact subgroup-coset
condition; here the ambient scheme and its supplied action are arbitrary.
