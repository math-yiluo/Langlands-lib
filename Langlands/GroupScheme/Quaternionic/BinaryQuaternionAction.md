# Binary quaternion product action

Authors: Worker 124.

This internal construction gives an actual homomorphism into binary matrix
units, its exact kernel on every coefficient ring, and preservation of the
quaternionic hyperbolic quadratic class. It derives these results by matrix
algebra from the published involution and reduced-norm constructions, and
from the accompanying `QuaternionConjugation` module. No external
classification or spin-cover comparison is assumed.

For a commutative ring `R` and an `R`-algebra `A`, `scalarSL` maps the actual
special-linear matrices to the units of `M₂(A)`. The homomorphism `uniform`
sends a unit `b` to `bI`. These images commute because the entries of the
first matrix are scalars. Their commuting product is `product`.

For an actual unit `ℓ`, `coordinateChange ℓ` is `diag(1,ℓ⁻¹)`, corresponding
to the row-coordinate change `(x,y) ↦ (x,yℓ⁻¹)`. Conjugating the product by
this matrix gives `action ℓ`. Its entries are

```
[ a b₀       c b₀ ℓ       ]
[ ℓ⁻¹(d b₀)  ℓ⁻¹(e b₀)ℓ ]
```

where the scalar special-linear matrix is `[a,c;d,e]` and the uniform unit
is `b₀`. Four entry lemmas state these formulas. `action_naturality`
proves compatibility with every pair of coefficient-ring maps that respect
the scalar maps.

If the scalar map `R → A` is injective, `product_eq_one_iff` and
`action_kernel` give the exact equation for the kernel: there is `r : R`
with `r*r = 1`, the special-linear matrix is `rI`, and the uniform unit is
the scalar image of `r`. The proof compares the four entries and uses the
determinant-one relation. This is the full square-root-of-one equation
over the ring; it does not replace the kernel by a set of field-valued signs.

The matrix `hyperbolicMatrix` is `[0,1;0,0]`. If `ℓ` belongs to the actual
alternating subspace of an involution `σ`, its inverse is also alternating.
The proof sandwiches an alternating witness by `ℓ⁻¹` and uses
`σ(ℓ⁻¹) = -ℓ⁻¹`. `scalar_preserves` explicitly writes the defect of the
scalar action as an alternating matrix, using the determinant relation.
If `b₀ℓσ(b₀) = ℓ`, `uniform_preserves` proves exact preservation of the
representative. Factoring the full product into these two actions proves
`action_preserves`, membership of its defect in the matrix alternating
subspace, in arbitrary characteristic.

For the target's central division algebra of dimension four and involution
with symmetric-space dimension three, `tensorAlternatingUnit` extends the
actual chosen unit from `QuaternionConjugation` to `R ⊗ D`.
`normOneAction` restricts the action to
`SL₂(R) × reducedNormOne(K,D,R)`. Scalars inject into this tensor algebra
by flatness over the ground field, so `normOneAction_kernel` gives the same
exact diagonal square-root-of-one kernel without an added injectivity
hypothesis. Over an infinite ground field, the proved all-coefficient
conjugation identity supplies `normOne_sandwich`, and
`normOneAction_preserves` proves preservation of the original hyperbolic
quadratic class on every commutative coefficient algebra, including
nonreduced ones.

This unit constructs homomorphisms of the concrete groups on coefficient
algebras. It does not yet construct the resulting group-scheme morphism,
prove that it is a central isogeny, identify it with a supplied spin cover,
or assert elementary generation in that cover.
