# The enlarged full logarithmic unit lattice

Let `E : Type v` be a number field. Write
`V = InfinitePlace E → ℝ`, let `V₀ = fullLogHyperplane E` be its
coordinate-sum-zero hyperplane, and let `M₀ = fullLogUnitLattice E`.
The imported full logarithm identifies `M₀` with the image of the actual
ring-integer units in `V₀`. This module constructs the full lattice

\[
M=M_0+\mathbf Z e\subset V,\qquad e(w)=1,
\]

and proves its discreteness, full real span, and stability under the
arithmetic permutation action.

## Construction and membership

`fullLogScalarLattice` is the integer span of the singleton real basis
`Module.Basis.singleton Unit ℝ`. The theorem `mem_fullLogScalarLattice`
identifies its elements exactly with integer casts:
`a ∈ fullLogScalarLattice ↔ ∃ z : ℤ, (z : ℝ) = a`.
The basis-span instances give its discrete subspace topology and its
`IsZLattice ℝ` instance.

`fullLogProductLattice E` is the product of `M₀` with this scalar
lattice, inside `V₀ × ℝ`. Its discrete topology is proved using the
continuous injective map to the product of the two lattice subtypes.
Its full-span proof applies the formula for the real span of a product
of sets containing zero and the two factors' full-span identities.

The imported real linear equivalence `fullLogSplit E` sends a vector
`x` to its centered component and its coordinate mean:

\[
x\longmapsto (x-\operatorname{mean}(x)e,\operatorname{mean}(x)).
\]

`augmentedFullLogUnitLattice E` is the pullback of
`fullLogProductLattice E` along this equivalence. The defining membership
criterion `mem_augmentedFullLogUnitLattice` says that the centered
component belongs to `M₀` and the mean is an integer.
The stronger explicit formula `mem_augmentedFullLogUnitLattice_iff` is

\[
x\in M\quad\Longleftrightarrow\quad
\exists y\in M_0,\ \exists z\in\mathbf Z,\quad y+ze=x,
\]

where Lean quantifies `y : fullLogUnitLattice E` and uses
`fullLogConstant E (z : ℝ)` for `ze`. The forward proof takes the centered
component and the integer supplied by scalar-lattice membership, then
uses reconstruction by the mean. The reverse proof computes the
centered component and mean of `y + ze`.

The discrete-topology and `IsZLattice ℝ` instances for `M` come from
Mathlib's pullback-lattice instances for a continuous linear equivalence.
Finite-dimensionality turns `fullLogSplit E` into the required continuous
linear equivalence. `augmentedFullLogUnitLattice_span` exposes the resulting
identity `Submodule.span ℝ (M : Set V) = ⊤`.

## Arithmetic invariance

For an arbitrary field `F : Type u` with `[Algebra F E]`, where `u` and
`v` are independent, the arithmetic automorphism group is `E ≃ₐ[F] E`.
The imported permutation action is

\[
(P_gx)(w)=x(g^{-1}\cdot w).
\]

`augmentedFullLogUnitLattice_invariant` proves that `x ∈ M` implies
`fullLogPermutation F E g x ∈ M`. Its proof uses equivariance of the
centered component, arithmetic stability of `M₀`, and invariance of the
coordinate mean. Applying it to `g⁻¹` also gives the reverse inclusion.
No Galois or cyclicity assumption is needed, and no assumption that `F`
is a number field is introduced. A field with a single infinite place
is included: then `V₀` is zero and the constant direction supplies the
full lattice.

## Provenance and scope

Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, proof of
Proposition 3.1, printed p.209 (PDF p.218), constructs `M = M₀ + ℤe`
and uses `V = V₀ + ℝe` to obtain a full invariant lattice. This module
specializes that construction to all infinite places, so the units are
ordinary ring-integer units. The exact registered source is
`milne-2020-class-field-theory`, SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.

The product-and-pullback presentation is an internal implementation of
the source's sum construction, justified by the explicit membership
formula above. Discreteness and spanning are supplied by the imported
Dirichlet unit lattice, Mathlib's basis lattice, and the real linear
splitting. The module does not assert a Herbrand quotient formula,
a cohomology comparison, or an identification with the integral
permutation representation. Those are subsequent obligations.
