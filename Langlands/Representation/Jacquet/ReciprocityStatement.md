# Character-twisted reciprocity through actual coinvariants

Worker 8 states this proposition using the accepted actual induction
construction of Worker 15 and actual normalizer-action construction of Worker 34.
The proposition is a target for a separate proof; defining it does not assume
its truth.

`Langlands.Jacquet.CharacterReciprocityStatement` has independent group,
source-module and target-module universes and complex coefficients. The group
is Hausdorff, is a topological group, and has an explicitly stated compact-open
neighborhood basis. Let `P` be a closed subgroup, `N ≤ P`, and assume that `P`
normalizes `N`. The representation `rho` of `G` and representation `sigma` of
`P` are smooth. Both `sigma` and a specified smooth scalar character `chi`
of `P` are trivial on `N`; the two triviality assumptions are written
separately and explicitly.

The statement is the complex-linear equivalence

`Hom_G(rho, Ind_P^G(chi * sigma)) ≃ Hom_P(chi^(-1) * rho_N, sigma)`.

Induction is the actual covariant smooth function space with right
translation. `rho_N` is the actual vector-space quotient by the span of
`rho(n)v - v`, with the descended `P`-action. The right-hand twist uses the
pointwise inverse of the same character used on the left. The equivalence is
characterized by

`(e F)([v]) = F(v)(1)`.

There are no module topologies, finite-dimensionality hypotheses, assumed
adjunction structures or arbitrary replacement representations. Closedness
of `N` is not needed for this algebraic quotient factorization, and no
topological quotient of the module is formed.

## Source correspondence and derivation

Read Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), Section 1.1, printed page 442 / PDF page 3, for the
group topology hypotheses; Section 1.8(a)-(b), printed pages 444-445 /
PDF pages 5-6, for the function convention and relation quotient; and
Section 1.9(b), printed page 445 / PDF page 6, for the adjunction.
In the trivial-unipotent specialization this gives ordinary smooth
subgroup Frobenius reciprocity. Read also Casselman, Chapter III,
Section 3, printed/PDF pages 3-4: the relation quotient, its universal
property in III.3.2, and the inverse-half-modulus convention preceding
the normalized reciprocity statement III.3.5.

The present formulation is derived from ordinary subgroup reciprocity and
that quotient universal property. An intertwiner into induction evaluates
to a `P`-map into `chi * sigma`. Since both factors are trivial on `N`,
this map kills the `N`-relations. It factors uniquely through `rho_N`.
Moving the scalar factor from the target to the source produces
`chi^(-1) * rho_N`; this determines the inverse sign. The inverse
construction sends a quotient intertwiner `A` to the function
`F_A(v)(g) = A([rho(g)v])`. Its covariance is exactly `chi * sigma`,
and a stabilizer of `v` fixes the entire function on the right.
These descriptions explain the actual equivalence and its evaluation
formula without assuming the theorem in a record field.

This is not a direct substitution `M=P, U=N` in BZ77 1.8, since their
Levi factor and unipotent subgroup intersect trivially. We retain the
full `P`-action on the quotient and derive the formula as above.
To obtain the parabolic theorem on the Levi group, one must use the
actual Levi projection/inflation and identify `chi` with the genuine
positive half-modulus of `P`. The inverse twist then becomes the
normalized Jacquet action. That specialization, including its
topological and modulus construction obligations, remains separate.
No arbitrary character is asserted to be a parabolic modulus.

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- SHA256:
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- Original:
  `C:/Central-Library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
- Literature ID: `casselman-2019-jacquet-module`.
- SHA256:
  `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
- Original:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.

## Published definitions and validation

The induction import is `Langlands.Representation.Induction.Definitions`,
using `Langlands.Induction.SmoothCharacter`, `normalizedSmoothInduced`,
and `eval`:

- `Langlands/Representation/Induction/Definitions.lean`:
  `2936c54b7596b3bfebc6f6f881c7a12c1eb34179290bfcb02068b1c50b8a3643`.
- Its Markdown:
  `9fc03b58ebdce911b5ff1046da802cb01419833f20eca318efbc53b354d5ac04`.

The Jacquet import is `Langlands.Representation.Jacquet.Coinvariants`,
using `Langlands.Jacquet.action` and `mk`:

- `Langlands/Representation/Jacquet/Coinvariants.lean`:
  `73e5003712204a35595095b0582ad64d931423aeecec2f6165c4c20d945a4566`.
- Its Markdown:
  `5e040cb16af3b1c72e0c7f1530881639ab055f9528703b9bc20de1931d098a00`.

Both complete construction pairs were read. Direct comparison with Library
commit `843c574c920aa9926ab56adf662c74b3cd4ed0e1` confirms that the local
Lean and Markdown files have the published bytes recorded above.
Their implementations remain with their authors and are imported as dependencies.

Induction imports `Langlands.Representation.Smooth.Definitions`,
`Langlands.Representation.Smooth.SmoothPart.Definitions`, and
`Langlands.Representation.Twist.Definitions`. These supply the actual
smoothness predicate, smooth-vector submodule, and `Langlands.twist`.
Their local Lean/Markdown files also match that Library commit byte for byte.
The algebraic Jacquet construction imports only Mathlib.
The scalar twist uses pointwise character inversion on the abelian group
of complex units.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The complete draft compiled natively without diagnostics, together with the
unchanged Jacquet construction dependency. A subsequent full elaborated
proposition print confirmed the three independent universes, the actual
intertwiner-space equivalence, the separate triviality assumptions on `N`,
the inverse character on the quotient, and evaluation at the identity.
The registered development check also passed the shared Lake build and
declaration inspection with zero warnings or errors, confirming a `Prop`
definition with independent universe parameters `uG`, `uV`, and `uW`.
Compilation and inspection are development evidence. No theorem proof,
independent semantic acceptance or publication of this proposition is claimed.
