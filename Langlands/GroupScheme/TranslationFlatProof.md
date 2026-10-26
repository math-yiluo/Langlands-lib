# Propagation of flatness by translations

The theorem `Langlands.GroupScheme.translationFlat.{u}` proves exactly the existing
`Langlands.GroupScheme.TranslationFlatStatement.{u}`. The statement and its
hypotheses are unchanged, in arbitrary universe and characteristic.

The proof uses Mathlib's actual group objects, rational sections, and right
translation isomorphisms `GrpObj.mulRight`. A scheme locally of finite type over
the algebraically closed base field is Jacobson. The inverse image of a closed
rational point under the surjective endomorphism is a nonempty closed set, so it
contains a closed point. Mathlib's `pointOfClosedPoint` turns this into a rational
section; `ext_of_apply_closedPoint_eq` proves its image is the original section.
Thus the endomorphism is surjective on rational sections. This argument needs
only the supplied scheme-point surjectivity, so the finite hypothesis is retained
in the exact target but is unnecessary in the implemented propagation argument.

Choose a rational closed point `y` of the given nonempty flatness open `U`.
For each rational source section `a`, form the target open that is the inverse
image of `U` under right translation by `f(a)`. The group homomorphism law proves
the equality of actual scheme morphisms
`translation(a) ≫ f = f ≫ translation(f(a))`. Restrict this equality over `U`.
On the left, flatness follows by composing a restricted isomorphism with `f`
restricted to `U`. On the right, cancellation of the restricted target
isomorphism proves flatness over the chosen inverse-translation open.

Every closed target point `x` is rational. Lift the rational section `x⁻¹ y`
through `f`; its target translation sends `x` to `y`, placing `x` in one of these
opens. Their union has empty complement: a nonempty closed complement would
contain a closed point by the Jacobson property. Flatness, local on the target,
then holds globally by `IsZariskiLocalAtTarget.of_iSup_eq_top`.

This is an internal derived proof of the published propagation statement. Its
translation strategy follows the statement's provenance discussion motivated by
Milne, *Abelian Varieties*, Proposition 8.1; it does not use the invocation of
Theorem 4.2(d) discussed there. It imports neither of the downstream global
flatness or isogeny conclusions. Generic open flatness and descent from an
algebraic closure remain separate obligations for the final consumer.

Authored by Worker 668. The reused group and point infrastructure is Mathlib's;
the published statement was authored by Worker 129 with specification coauthor
Worker 415.
