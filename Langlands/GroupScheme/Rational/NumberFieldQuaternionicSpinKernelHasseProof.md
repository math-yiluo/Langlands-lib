# The central part of the quaternionic spin Hasse kernel

Module `Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinKernelHasseProof`,
namespace `Langlands.GroupScheme`.

## The statement proved

The theorem `numberFieldQuaternionicSpinKernelHasse` proves
`NumberFieldQuaternionicSpinKernelHasseStatement` (module
`Rational/NumberFieldQuaternionicSpinHasseKernels`) at every universe.

Let `F` be a number field, `D` a central quaternion division algebra over `F` with an
orthogonal involution `σ` (symmetric subspace of dimension `3`), `n ≥ 4` and
`q : σ.QuadraticForms (Fin n)` nondegenerate. Let `π : G ⟶ σ.isometryGroup q` be a spin
cover (`σ.IsSpinCover q π`). For a finite Galois extension `L/F`, let `α` be a cocycle on
`GaloisCocycle.cover F L` with values in `kernel π`. If `(α.map (kernelι π)).LocallyTrivial`,
so its image in `G` is trivial after pullback to every completion of `F`, then that image
is a coboundary on the original cover.

This is the part of the Hasse principle for the spin group of `q` that concerns the image of
`H¹(F, μ₂)` in the exact sequence `Spin(F) → SU(F) → H¹(F, μ₂) → H¹(F, Spin)` of the double
cover (Kneser, *Lectures on Galois Cohomology of Classical Groups*, 1969, §5.11, sequence
(4), printed p. 101; the spin Hasse principle is §5.10, printed pp. 95–98).

## Proof

The proof applies `numberFieldQuaternionicSpinKernelHasse_of_boundaries` (module
`Rational/NumberFieldQuaternionicSpinKernelReduction`) to proofs of its four inputs:

1. `quaternionicSpinKernelMu` (module `Rational/QuaternionicSpinKernelMu`): the kernel of a
   simply connected central cover of `σ.normOneIsometryGroup q` is `μ₂`.
2. `quaternionicSpinLineSimilitudeBoundary` (module
   `Rational/QuaternionicSpinLineSimilitudeBoundary`): the Kummer class of the multiplier
   `Nrd(d)` of a line similitude `d c σ(d) = Nrd(d) c` dies in the cover.
3. `numberFieldQuaternionicSpinRealBoundary` (module
   `Rational/NumberFieldQuaternionicSpinRealBoundary`): at a real place where `D` stays
   division or the form stays anisotropic, a Kummer class that dies in the cover is the
   class of a square.
4. `numberFieldQuaternionicSpinorValue` (module `Rational/NumberFieldQuaternionicSpinorValue`):
   for `a ∈ Fˣ` that is a square at all such real places, there are a similitude `d` of a
   line of nonzero hermitian value and a unit `s ∈ Fˣ` with `Nrd(d) = a s²`.

In the reduction, statement 1 identifies the kernel with `μ₂`, and Kummer theory writes the
cocycle as the Kummer cocycle of some `a ∈ Fˣ`. Local triviality and statement 3 make `a` a
square at the relevant real places. Statement 4 gives the multiplier `Nrd(d) = a s²`.
If `z ∈ Lˣ` is the Kummer radical of `a`, then `zs` is a radical of `Nrd(d)` with the
same Galois ratios, since `s ∈ Fˣ`. Statement 2 trivializes their common Kummer image in
`G` on the cover defined by `L`.

## Provenance

The statement is part of Kneser's spin Hasse principle for skew-hermitian forms over
quaternion division algebras (Kneser, *Lectures on Galois Cohomology of Classical Groups*,
1969, §5.10–§5.11). The Lean proof follows the reduction above, whose inputs are proved in
the modules named in the list.
