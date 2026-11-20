# Labelled multiplicity removal and completion-valued descent

Author: Worker 773.

`TaylorLabelledMultiplicityRemovalStatement` takes a continuous
`L_λ`-representation of the absolute Galois group of a number field `E`.
Its geometric Frobenius characteristic polynomials at the good places are
`P_v^m` for monic degree-`n` polynomials `P_v` over `L` and one positive
multiplicity `m`. At the chosen label `E → L_λ` it has `n` distinct
Hodge–Tate twists of multiplicity `m`. The conclusion is a continuous
semisimple rank-`n` representation over a finite extension `Λ` of `L_λ`,
with the twists of multiplicity one at that label after extending the base
to `Λ`. Its characteristic polynomial to the power `m` equals that of
the input at every Galois element. At the original good places away from
the residue characteristic of `λ` it is unramified with polynomial `P_v`.

The input selects one Hodge–Tate label. It is a separate statement from
`TaylorMultiplicityRemovalStatement`, which records the decomposition
over `ℚ_ℓ` used in the trivial-coefficient case in Harris's printed sketch.
The single-label Sen operator gives the needed eigenvalue multiplicities
in the Lie algebra of the algebraic monodromy after extending scalars.
Semisimplification of the global representation preserves the local
Hodge–Tate decomposition. All-element characteristic powers follow by
Chebotarev and closedness of the monic-power locus. On a maximal torus
of the identity component, each weight space therefore has dimension
divisible by `m`. The `n` distinct Sen eigenvalues of multiplicity `m`
then force the torus weight spaces to have dimension exactly `m`.

For the disconnected step one takes the stabilizer `N` of a Borel and a
maximal torus `T` of the connected component `H⁰`. The intersection
`H⁰ ∩ N` is `T`, and `N/T` is finite. For a lowest weight which is also a
vertex of the weight polytope, an element of the weight stabilizer acts
semisimply on its weight space since a positive power belongs to `T`,
which acts scalarly there. An orbit of other weights cannot average to
that vertex. Thus on multiplying by a generic torus element its
eigenvalues on the extremal weight cannot come from other weight orbits.
The characteristic-power condition forces just one eigenvalue on the
`m`-dimensional space. The orbit of the corresponding isotypic summand
can be removed in `m` copies. Iteration gives the semisimple representation
over the algebraic closure. The finite field model and retention of
Hodge–Tate weights use finite-dimensional scalar extension and the
subquotient property of Hodge–Tate representations.

`RegularHodgeTateCoefficientDescentStatement` is the fixed-coefficient
step. It starts with a continuous semisimple representation over a
finite extension `Λ/L_λ` whose trace at every Galois element is in `L_λ`.
It also assumes a regular Hodge–Tate decomposition after restriction via
`E → L_λ → Λ` at the identity coefficient label. It concludes that there
is an actual `L_λ`-representation whose scalar extension is isomorphic
to the given one, and which has the same regular Hodge–Tate decomposition
at `E → L_λ`. `IsCoefficientScalarExtension` uses a linear isomorphism
with the actual tensor product and compares the actions of all elements.

For this descent, the trace pairing on the semisimple image algebra over
`Λ` is nondegenerate in characteristic zero. Choose a basis from the
Galois matrices. Its Gram matrix is over `L_λ` by trace rationality, and
coordinates of every Galois matrix are over `L_λ` by the same pairing.
The span over `L_λ` is therefore a form of the image algebra. In each
simple component the endomorphism division algebra `D` of the simple
module has dimension `e d²` over `L_λ`, with center degree `e` and Schur
index `d`. Over the algebraic closure the simple module has `d` copies
of each of the `e` associated absolute constituents. The regularity
assumption makes a nonzero graded piece of this simple module at the
chosen label have dimension `d`. To compute the grading over `L_λ`,
first descend the Hodge–Tate decomposition along a finite extension
using Tate's fixed field and twist invariants and finite Galois descent.
That graded piece is a module over `D`, since the endomorphisms commute
with the Galois action. Thus `e d²` divides `d`, forcing `e = d = 1`.
The resulting scalar model is continuous and retains the rank and
unramified polynomials by faithful scalar extension.

These two statements separate the local extraction from coefficient
descent. Applied using `tr(A) = m · tr(U)`, the descent step gives a
representation at each actual coefficient completion of the same
number field.

## Sources

- M. Harris, *Supercuspidal representations in the cohomology of Drinfel'd
  upper half spaces*, Invent. Math. 129 (1997), §3, pp. 102–103, for the
  printed sketch of Taylor's argument. Registered
  `harris-1997-drinfeld-cohomology`, SHA256
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- M. Harris and R. Taylor, *The Geometry and Cohomology of Some Simple
  Shimura Varieties* (2001), VII.1.9, pp. 227–228, for the regular
  graded pieces at a selected embedding. Registered
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
- J.-P. Serre, *Linear Representations of Finite Groups*, §12.2,
  pp. 92–94, for the simple algebra and Schur index calculation.
  Here it is applied to the finite-dimensional semisimple image algebra
  of the continuous representation. Registered
  `serre-1977-linear-representations`, SHA256
  `b6c0432dfc882618110c25a489c8fa0d93f1e64da4fba4950eb90c1b8348dcc2`.
