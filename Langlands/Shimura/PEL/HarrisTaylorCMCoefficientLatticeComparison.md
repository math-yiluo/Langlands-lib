# Actual CM lattice comparison on common coefficient kernels

This internal construction transports the actual canonical lattice inclusion
at nested compact levels to the original opposite CM level groups. It builds
common small coefficient levels, their finite residual quotient diagram,
and an equivariant map of the two full coefficient diagrams.

The main construction has the following actual arithmetic inputs, in the
single universe used by the imported CM level tower:

- Number fields `E` and `F`, with `E` totally real and `F` totally complex
  and CM, an `E`-algebra structure on `F`, and `IsQuadraticExtension E F`.
- A ring `A` with its `E`, `F`, and rational algebra structures, the scalar
  towers `E → F → A`, `ℚ → E → A`, and `ℚ → F → A`, and
  `Module.Finite ℚ A`.
- A natural number `n` and the actual central-simple unitary datum
  `D : CentralSimpleUnitaryData E F A n`.
- A coefficient number field `K`, a finite-dimensional `K`-module `W`,
  and `ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`.
- A finite place `p` of `ℚ`, actual small CM levels `U` and `V`, and only
  the subgroup-containment hypothesis `V.obj.subgroup ≤ U.obj.subgroup`.

All coefficient modules retain the integral product ring
`R = HarrisCoefficientIntegers K p`. The two lattices are the actual
canonical lattices constructed separately at
`CompactOpenLevel.inverseOpposite V.obj` and
`CompactOpenLevel.inverseOpposite U.obj`, in the same original tensor
coefficient module. No lattice comparison, normality of `V` inside `U`,
or output map is supplied as an input. The generic auxiliary theorem
`CompactOpenLevel.inverseOpposite_mono` applies to any topological group;
the later declarations use the above arithmetic inputs. Some subgroup
identities and normalization theorems omit unused CM or scalar-tower
classes explicitly in Lean.

`CompactOpenLevel.inverseOpposite_mono` transports the level inclusion.
`cmHarrisTorsionSystemInclusion` uses `harrisTorsionSystemInclusion` on these
ordinary levels, transporting both actions by the original inverse-unop
isomorphisms. The group operators agree on their ambient vectors. The `mk`
formula retains the same vector, and the `transition` theorem retains all
original exponent reductions. This first construction allows every scalar
`m`, including zero.

For nonzero `m`, let `V_k` be the coefficient kernel level constructed using
the lattice at `V`, and let `T_k = V ∩ U_k` be the restricted original
coefficient kernel level. `cmHarrisLatticeCommonLevel` constructs the actual
identity-Hecke intersection

\[
N_k=V_k\cap T_k.
\]

Its subgroup formula, inclusions into both levels and `V`, normality
inside `V`, and antitonicity are proved. Its subgroup inside `V` is exactly the intersection
of the kernels of the two transported torsion actions. Thus both actions
factor through `Q_k = V/N_k`. The levels form a functor on `ℕᵒᵖ` using the
original identity-transporter inclusions. The finite groups `Q_k` form a
functor using the original quotient maps.

The natural maps from `Q_k` to the residual groups for `V_k` and `T_k`
are induced by these actual subgroup inclusions and retain representatives.
Restricting the existing two coefficient diagrams along these maps constructs
`cmHarrisLatticeCommonOwnCoefficients` and
`cmHarrisLatticeCommonOriginalCoefficients`. Their underlying functors are
the complete original coefficient functors at `V` and `U`, respectively,
with the latter retaining its action restricted to `V`.
Their equivariance fields follow by quotient induction from the original
torsion-system commutation laws.

`cmHarrisLatticeCommonCoefficientInclusion` is a morphism of these equivariant
diagrams. Its underlying natural transformation is the actual transported
torsion inclusion with the actions forgotten. Quotient induction proves its
equivariance. Its `mk` theorem gives the class of the same included ambient
vector, and its `transition` theorem records every exponent square.

Exponent zero remains allowed throughout; the nonzero restriction is on
`m` when constructing actual compact open kernel levels and finite residual
groups. The torsion-system inclusion itself has no nonzero-scalar premise.

This pair is an internal deduction from `HarrisLatticeLevelInclusion` and
`HarrisTaylorCMCoefficientCoarseRestriction`, including their published
coefficient, common-level and residual-quotient dependencies. It introduces
no external-source assertion. It asserts no injectivity or invertibility of
the reduced inclusion, no equality of the two lattices, and no rational
adic lattice independence. Descent of this comparison on actual geometric
CM covers is a further step. The containing task's representability,
arithmetic existence and canonical-model obligations remain.
