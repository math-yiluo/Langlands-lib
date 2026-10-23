# Inverse weight spaces of the actual complex Kottwitz cocharacter

This module constructs inverse-weight submodules from the actual Kottwitz
cocharacter and identifies their ranks with the Hodge function of the
constructed positive real homomorphism. Its provenance is internal: it derives
these objects and identities from `ComplexKottwitzMatrices`, `RealReflex`, and
Mathlib's coordinate-submodule equivalence. The conventions and source
provenance of the imported cocharacter and real Hodge function are retained.
No diagonal formula or rank conclusion is supplied as a hypothesis.

## Generic inverse-weight submodule

Let `S` be any commutative complex algebra and `n` a natural number. Given a
matrix family `a : Sˣ → Matrix (Fin n) (Fin n) S`,
`ComplexMatrix.inverseWeightSpace a` is the `S`-submodule

\[
 W_{-1}(a)=\{v\in S^n\mid a(u)v=u^{-1}v\ \text{for every }u\in S^\times\}.
\]

The inverse is the inverse of a unit. The construction does not require the
family to be multiplicative; the submodule axioms follow from linearity of
matrix-vector multiplication and commutativity of scalar actions. In its
application below the family comes from a group-scheme cocharacter.

For any decidable predicate `p` on `Fin n`,
`inverseWeightSpace_diagonal` identifies the submodule for the diagonal
family with entries `u⁻¹` at `p` and `1` elsewhere as

\[
 W_{-1}=\bigcap_{j:\neg p(j)}\ker(\operatorname{proj}_j).
\]

To prove that a vector has zero coordinates outside `p`, the implementation
evaluates the defining identity at the unit `-1`. At such a coordinate it
obtains `v j = -v j`, hence `(2 : ℂ) • v j = 0`. Since the complex scalar `2`
is nonzero, this forces `v j = 0`. The reverse inclusion follows coordinate
by coordinate from the diagonal formula. No domain or nontriviality
hypothesis on `S` is needed for this equality.

When `S` is nontrivial, `finrank_inverseWeightSpace_diagonal` proves

\[
 \operatorname{finrank}_S W_{-1}=\#\{j\in\mathrm{Fin}\,n\mid p(j)\}.
\]

The proof uses `LinearMap.iInfKerProjEquiv` for the complementary coordinate
sets to identify the submodule with functions on the selected coordinates,
then applies the rank formula for that finite free module. It works over
commutative complex algebras, not only fields.

## Evaluation of the actual cocharacter

Retain the number fields, scalar towers, central simple algebra with
second-kind involution supplied by `D : CentralSimpleUnitaryData E K A n`,
and `C : HarrisSignatureCharts D.toSecondKindInvolution n Φ`. These are the
same hypotheses as the imported actual cocharacter matrix calculation.
Let `T` be any test scheme over `Spec ℂ`, and write
`S = AlgebraInvolution.complexTestAlgebra T`. Its underlying ring is
`Γ(T,O_T)`; the complex algebra structure comes from the structure morphism.
For a real embedding `τ`, put

\[
 r_\tau=\begin{cases}n-1&\tau=C.\mathrm{distinguished},\\n&\text{otherwise}.\end{cases}
\]

`kottwitzCocharacter_unit_matrices` evaluates the actual cocharacter
`D.kottwitzCocharacter C true` at the `Gm` point corresponding to `u : Sˣ`
under `GroupScheme.Gm.pointsEquiv`. It gives the pair

\[
 \left(\operatorname{diag}(u^{-1}\text{ for }j<r_\tau;1\text{ otherwise}),
       \operatorname{diag}(1\text{ for }j<r_\tau;u^{-1}\text{ otherwise})\right).
\]

This follows from `kottwitzCocharacter_matrices` and cancellation of the
point equivalence with its inverse. The cocharacter retains the imported
convention of conjugation before inversion and uses the first factor of
the split Deligne torus.

`kottwitzMatrixWeightSpace C T τ selected` applies the generic inverse-weight
construction to these actual matrices. Here `selected = true` chooses the
first matrix and `false` the second; this Boolean selects a target matrix
factor, while the source cocharacter stays fixed at its first factor.
`kottwitzMatrixWeightSpace_diagonal` identifies it with the diagonal
inverse-weight space whose coordinate predicate is

\[
 p(j)=\begin{cases}j<r_\tau&\text{if selected},\\
                   \neg(j<r_\tau)&\text{otherwise}.\end{cases}
\]

`kottwitzMatrixWeightSpace_eq` gives the corresponding intersection of
coordinate kernels. These equalities include nonaffine, nonreduced and empty
test schemes. No representability or existence conclusion is assumed.

Under `[Nontrivial Γ(T.left, ⊤)]`, the two rank lemmas give respectively
`rτ` and `1` at the distinguished place, and `n` and `0` at every other
place. The selected-factor proof counts the indices below `rτ`. The
conjugate-factor proof counts their complement and uses `C.rank_gt_one`
to simplify `n - (n - 1)` to `1`. The nontriviality assumption is needed for
the finite-free rank calculation and excludes the zero ring of sections.

## Alignment with the real Hodge function

For a complex embedding `i : K →+* ℂ`, `kottwitzWeightSpace C T i` uses
`τ = realPlaceBelow E i` and selects the first matrix exactly when
`i = Φ τ`, otherwise the second. This is the same embedding-selection rule
as `standardHodgeFunction` and `D.realHodgeFunction C`.

`finrank_kottwitzWeightSpace` proves, under the same nontriviality hypothesis,

\[
 \operatorname{finrank}_S(D.\mathrm{kottwitzWeightSpace}\ C\ T\ i)
   = D.\mathrm{realHodgeFunction}\ C\ i.
\]

The proof rewrites the real Hodge function using `realHodgeFunction_eq` and
`HarrisSignatureCharts.hodgeFunction_apply`, then applies the appropriate
matrix-factor rank theorem. Thus the real Hodge numbers are recovered from
the inverse weights of the actual complex cocharacter at every such test
scheme, with the same signature charts and embedding convention.

This is a weight-space and rank comparison. It does not prove chart
independence, conjugacy of cocharacters, or identify a Galois stabilizer of
cocharacter conjugacy classes. Those comparisons, the scheme splitting,
smoothness and reductivity, and the remaining PEL geometry and coefficient
descent are separate obligations of the surrounding construction.
