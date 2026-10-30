# Zero tests for tensor products of actual sections

`Langlands.SchemeModule.TensorSectionZeroStatement` is an internal
Prop-valued package for the published actual `Scheme.Modules` tensor
product, `tensorSection`, and `pullbackSection`. It quantifies over
arbitrary schemes in one arbitrary universe, arbitrary module sheaves,
and arbitrary global sections.

The five conjunction clauses assert, in order:

1. A tensor section with zero first factor is zero.
2. A tensor section with zero second factor is zero.
3. If the second section's morphism from the structure module is an
   isomorphism, its tensor product with a first section is zero exactly
   when the first section is zero.
4. The symmetric cancellation assertion when the first section's
   morphism is an isomorphism.
5. Pullback of a tensor section is zero exactly when the tensor section
   of the two actual pulled-back sections is zero. The two sides live in
   canonically isomorphic module sheaves; this is an equivalence of zero
   conditions, not a claimed definitional equality of sections.

The isomorphism condition in clauses 3 and 4 is a global frame condition.
No claim is made that arbitrary nonzero factors reflect zero, even for
line bundles: this would fail over rings with zero divisors, including
rings of dual numbers. There are no field, local freeness, smoothness,
properness or finiteness hypotheses. The pullback comparison in clause 5
uses the Library's actual tensor comparison in its eventual proof.

This is derived internal section calculus, needed to form translated
sections in the separating-line-bundle construction. The statement
claims no external literature theorem and proves none of its clauses.
No projectivity or ample-existence input is involved.
