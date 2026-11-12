# The inverse-right-regular representation of a finite algebra's units

All-test construction: Worker 118. The corepresented presentation is an independently reviewed supporting contribution.

Let `A` be a possibly noncommutative algebra over a field `k : Type u`, with
a supplied finite basis `b : Basis (Fin d) k A`. This internal construction
defines an actual faithful group-scheme representation

`FiniteAlgebraUnits.rightRegularRepresentation b :
 FiniteAlgebraUnits.groupScheme b ⟶ GL_d`.

For a commutative `k`-algebra `R`, `rightMulMatrix b R x` is the matrix,
in the base-changed basis, of `y ↦ y*x` on `R ⊗[k] A`. Multiplication reverses
the order of these matrices. Thus `rightRegularUnits b R` sends a unit `g`
to the matrix of `y ↦ y*g⁻¹`, which is a group homomorphism.

The multiplication and inverse identities follow from associativity and the
unit identities. The matrix determines right multiplication, and evaluation
at one recovers its multiplying element. This proves injectivity, including
when the algebra is the zero ring or `d = 0`.

The coefficient-change identity is proved on pure tensors and extended by
additivity. Combining it with the published all-test point coordinates for
finite-algebra units and `GL_d` gives a natural homomorphism on points.
`homOfPoints` constructs the actual group-scheme morphism.
`pointsEquiv_rightRegularRepresentation` gives its formula on every test
scheme. Its underlying morphism over `Spec k`, and its underlying morphism
of schemes, are monomorphisms by injectivity on all test points.

This is an internal finite-free construction. No closed-immersion,
reductivity, split-torus diagonalization, or weight-support conclusion is
asserted here. Its intended application is the faithful action of a
quaternionic isometry group on the row spaces of its matrix algebra.

The same coefficient-algebra homomorphisms also define
`rightRegularNatTrans`, a natural transformation of the represented unit
functors. `rightRegularHom` is the actual group-scheme morphism obtained
from this transformation by `Corepresented.groupSchemeMap`.
`rightRegularHom_affineMatrix` identifies its matrix with
`rightRegularUnits` on every affine coefficient point, and
`mono_rightRegularHom` proves that its relative scheme morphism is a
monomorphism using all scheme tests. This presentation retains its own
construction alongside `rightRegularRepresentation`; both use the shared
`rightMulMatrix` and `rightRegularUnits` definitions above.
