# External tensors of finite-dimensional simple complex modules

The theorem `Langlands.algebraExternalTensorSimple` proves the published
`Langlands.AlgebraExternalTensorSimpleStatement`, with independent algebra
universes `u₁`, `u₂` and module universes `v₁`, `v₂`. It is the first assertion
of the Scholium in Renard III.1.14, printed pp.66–67 / PDF pp.72–73 of the
registered 9 July 2026 edition
`renard-2026-representations-groupes-reductifs-padiques` (SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
The target's paired Markdown explains its tensor-product-algebra reading of
the source's notation. This proof preserves that target and its imports.

For unital complex algebras `A₁`, `A₂`, let `V₁`, `V₂` be finite-dimensional
simple modules with the stated scalar towers. The internal abbreviation
`Langlands.AlgebraTensor.action` is the exact algebra homomorphism occurring
in the statement, built from the two scalar actions and
`Module.endTensorEndAlgHom`. Its pure-tensor formula is `action_tmul`.

The lemma `action_surjective` applies the published Burnside theorem
`Langlands.RankOneGraded.exists_forall_eq_smul_of_isSimpleModule` separately
to the two modules. Every endomorphism of each factor is therefore the action
of an algebra element. The finite-projective tensor-Hom equivalence
`homTensorHomEquiv` expresses an endomorphism of `V₁ ⊗[ℂ] V₂` as a sum of
tensors of factor endomorphisms. Tensor induction, the pure-tensor formula
and additivity show that every such endomorphism is in the external action's
image. Burnside's theorem in the imported module uses Schur's lemma over an
algebraically closed field and Jacobson density on a finite basis.

The lemma `stable_eq_bot_or_top` takes a nonzero vector `x` in a nonzero stable
complex subspace. A linear functional taking value one at `x` yields, for any
vector `y`, the rank-one endomorphism sending `x` to `y`. Surjectivity of the
action and stability place every `y` in the subspace. It is thus the whole
space. Simple modules are nontrivial, and the tensor product of nontrivial
vector spaces over a field is nontrivial. This proves both clauses of the
published statement.

The helper declarations are internal constructions for this proof, derived
from the published target and Mathlib tensor linear algebra. This module
proves external simplicity only; it does not assert factorization or
uniqueness of factors, or any group representation theorem.
