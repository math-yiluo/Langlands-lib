# Actual reduction kernels and compatibility of defect corrections

For any map of base schemes `r : S₀ → S`, `reductionPointHom r G T` pulls an actual `T`-valued point of `G` back to a point of the actual group-scheme base change. It is a group homomorphism because the pullback functor is monoidal. `reductionKernel r G` records its kernel on every test scheme and proves stability under restriction of tests.

This is the pointwise actual kernel. No assertion identifies it with the tensor-extension functor of a module on every test scheme. In infinitesimal deformation applications such tensor descriptions need the appropriate flatness hypotheses on the tests where they are used.

The remaining lemmas verify that the actual morphism constructions in `MultiplicativityDefect` behave as required under reduction:

- `correctedHom_hom` identifies the underlying map of the group-valued Yoneda reconstruction with the supplied corrected scheme map, by evaluating its pointwise characterization at the identity of the source.
- `multiplicationDefect_baseChange_eq_one` proves that a scheme map reducing to a group homomorphism has defect reducing to the identity. Pullback preserves the group operations on points, and the reduced homomorphism preserves multiplication.
- `correctedHom_baseChange_eq` proves that a regular correction reducing to the identity preserves the prescribed reduction of the resulting homomorphism.
- `homomorphismDifference_baseChange_eq_one` proves that the regular difference of two actual homomorphisms with equal reductions takes values in the reduction kernel.

These results need no affineness, smoothness, flatness or nilpotence assumptions. They express only functorial and group-theoretic compatibility. They construct neither a scheme-map lift nor an infinitesimal coefficient model or a correcting cochain.

This is an internal derived construction using the Library's actual base-change functor and actual defect/correction morphisms, together with Mathlib's monoidal maps on group objects. It introduces no additional literature assertion.
