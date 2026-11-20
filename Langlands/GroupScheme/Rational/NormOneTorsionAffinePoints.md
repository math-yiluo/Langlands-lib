# Affine points of norm-one torsion

Let `B/F` be a finite field extension and `n` a natural number.
`WeilGm.normOneTorsion F B n` is the `n`-torsion group scheme of the
actual kernel of the Weil restriction norm `Res_{B/F} Gₘ → Gₘ`.
For a commutative `F`-algebra `R`, `normOneTorsionAffineEquiv` identifies
its affine `R`-points with the subgroup of `(B ⊗[F] R)ˣ` of units whose
`n`-th power and determinant norm are both one.

The forward map is the composite of the torsion and norm-kernel
inclusions followed by the affine Weil-restriction coordinates.
Under these coordinates the group scheme norm agrees with the tensor
unit norm, by the compatibility of the determinant norm with the
canonical global-sections isomorphism for an affine test. Each unit
satisfying the two equations has unique lifts through both kernel
inclusions. This gives the inverse and proves that the map is a
multiplicative equivalence. The tensor-unit map commutes with every
change of `R` via the induced homomorphism on the right tensor factor.
