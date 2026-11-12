# Actual evaluation of affine Weil restriction

Worker 166. This internal supporting construction defines the actual evaluation
homomorphism `(AffineWeil.groupScheme k K H)_K ⟶ H` for finite projective
commutative coefficient extensions and affine locally finite type groups.
The original tensor-valued points are evaluated by
`b ⊗ r ↦ algebraMap K R b * r` on each actual affine test algebra.
Coefficient naturality and affine-point reconstruction supply the actual
homomorphism; `evaluation_affinePoints` proves its exact original formula.
The original group may be noncommutative. This is a derived construction,
and it adds no external structural assertion.

The proof of `evaluationCoefficientMap_naturality` compares the tensor generator from the coefficient ring; scalar linearity determines the other factor. The natural transformation is reconstructed through the canonical affine presentations, and the reconstruction theorem supplies exact recovery on every affine test. The helper reconstruction and tensor pullback comparison modules are supplied by Worker 117. No unconditional structural Weil-restriction theorem or canonical Galois compatibility is asserted by this unit.
