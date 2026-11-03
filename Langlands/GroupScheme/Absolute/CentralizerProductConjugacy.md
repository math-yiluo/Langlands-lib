# Conjugacy and rational points of the centralizer product

Internal implementation by Worker 1438. This module derives a conditional
centralizer-product factorization from the published group-scheme conjugacy,
represented-subgroup and cocharacter-restriction interfaces and the accompanying
closure-rigidity helper. It assumes no assertion from external literature.

Over an arbitrary base scheme, an all-test inverse-conjugation condition for a
base point `r` gives an actual group homomorphism into a monic subgroup `B`.
`inverseConjugateHom` factors the composite of the original homomorphism with
inner conjugation by `r⁻¹` through the represented range of `B`. Cancellation
identifies its values with the previously constructed unique conjugate points.

For a cocharacter `χ` whose full range lies in `B`, suppose this inverse-conjugated
homomorphism is conjugate to the restricted cocharacter by a base point `x` of
`B`. Write `v` for the ambient image of `x`. The all-test conjugacy equation
shows that `r v⁻¹` centralizes `χ` after every refinement. Its membership in the
dynamic centralizer therefore gives an actual lift `m` into any supplied
representative `j : M → G`. The point `(m,x)` maps to `r` under multiplication.
This argument applies to trivial and noninjective cocharacters as well.

Over any field, when `M` and `B` are smooth, affine and connected and `B` is
closed, closure rigidity identifies the projection of the inverse-conjugated
cocharacter at each base point of the reduced product closure with that of the
restricted cocharacter. The projection `q : B → D` is supplied, with split torus
target `D`; no quotient or surjectivity hypothesis is required for that equality.
Combining this equality with an explicit same-projection conjugacy hypothesis
shows that every rational point of the closure lifts to the actual product.

The module does not prove same-projection conjugacy, construct a solvable torus
quotient, establish closedness of the product image, or prove the Borel-intersection
statement. These are separate remaining obligations. Algebraic closure of the
field is not needed for the conditional statements here.
