# Conjugacy invariance of inverse-weight spaces

This module constructs linear equivalences between inverse-weight submodules
under intertwiners and matrix-unit conjugation, then applies them to families
of points of the actual complex Harris group. Its provenance is internal:
it uses the inverse-weight submodule from `ComplexWeightSpaces`, Mathlib's
matrix-to-linear-equivalence construction, and the multiplicative point
equivalence from `ComplexGroupPoints`. It introduces no new source convention.

## Intertwining and matrix conjugation

Let `S` be a commutative ring, `n` a natural number, and let
`a,b : Sˣ → Matrix (Fin n) (Fin n) S`. Write

\[
W_{-1}(a)=\{v\in S^n\mid a(u)v=u^{-1}v
                 \text{ for every }u\in S^\times\}.
\]

Although the imported module also studies complex algebras, the definition of
this submodule and the equivalences here need only a commutative ring.
Neither multiplicativity of the families nor nontriviality of `S` is assumed.

Suppose an `S`-linear equivalence `e : Sⁿ ≃ₗ[S] Sⁿ` satisfies
`b(u)(e(v)) = e(a(u)v)` for every unit `u` and vector `v`.
`mem_inverseWeightSpace_iff` proves that `e(v)` lies in `W₋₁(b)` exactly when
`v` lies in `W₋₁(a)`. The proof rewrites the intertwining equation, moves the
inverse scalar through the linear equivalence, and cancels its injective
underlying function.

`inverseWeightSpaceEquiv` restricts `e` to an actual linear equivalence
`W₋₁(a) ≃ₗ[S] W₋₁(b)`. Its inverse is the restriction of `e.symm`.
Membership follows from the preceding equivalence; the inverse identities,
additivity and scalar compatibility follow from those of `e`.

For a matrix unit `g`, `inverseWeightSpaceConjEquiv` specializes this to

\[
W_{-1}(a)\ \simeq_S\
W_{-1}\bigl(u\longmapsto g\,a(u)\,g^{-1}\bigr).
\]

Here the inverse is the inverse of the matrix unit. The implementation uses
`(Matrix.GeneralLinearGroup.toLin g).toLinearEquiv`; its action is
matrix-vector multiplication by `g`. The intertwining identity follows by
associativity and cancellation of `g⁻¹g`. Thus this is a constructed
equivalence of submodules, not an assumed rank equality.
`finrank_inverseWeightSpace_conj` then applies `LinearEquiv.finrank_eq`.
It requires no freeness or finite-generation hypothesis and includes the
zero ring; it asserts equality of Mathlib's numerical `Module.finrank`.

## Families of actual Harris group points

Retain the totally real number field `E`, totally complex number field `K`,
quadratic extension and compatible scalar towers on `A` used by
`D : CentralSimpleUnitaryData E K A n` and
`C : HarrisSignatureCharts D.toSecondKindInvolution n Φ`.
For any test scheme `T` over `Spec ℂ`, let
`S = AlgebraInvolution.complexTestAlgebra T`, the actual ring of global
sections with its structural complex algebra instance. Write
`G = D.complexRationalGroupScheme`.

Given an arbitrary family `a : Sˣ → G(T)` and a real embedding `τ`,
`complexPointWeightSpace C T a τ` is the inverse-weight submodule of
the matrix family

\[
u\longmapsto
\bigl(D.\mathrm{complexGroupPointsEquiv}\ C\ T\ (a(u))\bigr)_\tau.
\]

It uses the first matrix factor at the selected CM embedding above `τ`.
The full point equivalence also carries the common scalar multiplier, but
the weight submodule here uses its matrix component. No homomorphism
condition is required on `a`.

For every actual point `g ∈ G(T)`, `complexPointWeightSpaceConjEquiv`
constructs an `S`-linear equivalence from this space to the one for
`u ↦ g a(u) g⁻¹`. The proof uses multiplicativity and inverse preservation of
the full point equivalence. Projecting to `τ` identifies the conjugated
matrix family with conjugation by the corresponding matrix unit, so the
generic equivalence applies.
`finrank_complexPointWeightSpace_conj` gives equality of their numerical
ranks. These constructions allow arbitrary test schemes, including
nonaffine, nonreduced and empty schemes, without a section-ring
nontriviality hypothesis.

## The actual Kottwitz family

For the family obtained by evaluating the actual first-source-factor
cocharacter `D.kottwitzCocharacter C true` at the `Gm` point associated to
each unit `u`, `complexPointWeightSpace_kottwitz` identifies this submodule
with `D.kottwitzMatrixWeightSpace C T τ true`. This equality is definitional:
the first projection of the full point equivalence is the previously
constructed first matrix coordinate.

Under `[Nontrivial Γ(T.left, ⊤)]`,
`finrank_complexPointWeightSpace_conj_kottwitz` proves that the inverse-weight
rank of every conjugate of this actual family is

\[
r_\tau =
\begin{cases}
n-1&\tau=C.\mathrm{distinguished},\\
n&\text{otherwise}.
\end{cases}
\]

The proof first removes the conjugation using the constructed equivalence,
then uses the preceding definitional identification and
`finrank_kottwitzMatrixWeightSpace_true`. The rank hypothesis is required
only for this explicit signature calculation. The actual cocharacter
retains conjugation before inversion and the source-factor convention of
the imported construction.

This supplies conjugacy invariance on each fixed test scheme and in its
selected matrix factors. It does not assert that equality of these ranks
implies conjugacy, compare different signature charts, construct a Galois
action on scheme cocharacters, or identify the stabilizer of their
conjugacy classes. Those remain further steps toward reflex-field alignment.
