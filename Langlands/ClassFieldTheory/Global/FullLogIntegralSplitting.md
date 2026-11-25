# Integral splitting of the augmented full logarithmic lattice

For a number field `E : Type v`, let `M₀ = fullLogUnitLattice E` be the
image of the actual ring-integer units under the full logarithm, inside
the coordinate-sum-zero hyperplane. Let `M = augmentedFullLogUnitLattice E`
be the lattice `M₀ + ℤe` in `InfinitePlace E → ℝ`, where `e` is the
all-ones vector. This module constructs an integer linear equivalence

\[
\operatorname{fullLogIntegralSplit}:M\simeq_{\mathbf Z} M_0\times\mathbf Z
\]

and proves that the actual arithmetic action becomes the action on
`M₀` together with the trivial action on the integer factor.

## Maps and inverse identities

`fullLogLatticeAssemble E` is the integer linear map
`M₀ × ℤ →ₗ[ℤ] M` defined by `(y,z) ↦ y + ze`.
Its membership proof uses the imported exact sum characterization of `M`.
Additivity follows by regrouping terms; integer scalar compatibility is
checked at each infinite place using compatibility of integer casts in `ℝ`.
The theorem `fullLogLatticeAssemble_apply` exposes this formula after
coercion to the real coordinate space.

`fullLogLatticeAssemble_bijective` proves injectivity by applying the
coordinate mean and centered projection to an equality of assembled
vectors. The mean recovers the real cast of `z`, and injectivity of the
integer cast recovers `z`; the centered projection recovers `y`.
Surjectivity follows from `mem_augmentedFullLogUnitLattice_iff`.
`fullLogIntegralSplit E` is the inverse of the integer linear equivalence
obtained from this bijective map.

The following formulas specify the equivalence completely:

- `fullLogIntegralSplit_symm_apply`: the inverse sends `(y,z)` to `y + ze`.
- `fullLogIntegralSplit_fst`: the first component, viewed in the hyperplane,
  is `fullLogCentered E x`.
- `fullLogIntegralSplit_snd`: the real cast of the integer second
  component is `fullLogMean E x`.

The last two identities follow by writing `x` in the image of the inverse
equivalence and computing its centered component and mean.

## Restricted arithmetic actions and equivariance

Let `F : Type u` be a field with `[Algebra F E]`, where `u` and `v`
are independent. The acting group is the actual automorphism group
`E ≃ₐ[F] E`. No number-field assumption on `F`, Galois assumption, or
cyclicity assumption is needed.

`fullLogUnitLatticeAut F E` is a monoid homomorphism from this group
to the integer linear automorphisms of `M₀`. It restricts
`fullLogHyperplaneAut F E` using the established arithmetic stability
of the logarithm image. Its inverse uses the action of `g⁻¹`.
`augmentedFullLogUnitLatticeAut F E` similarly restricts the full
coordinate permutation `fullLogPermutation F E` to `M`.
The two `*_apply` lemmas identify the underlying vectors with the
original actions. The inverse laws and homomorphism laws descend by
subtype extensionality from those of the ambient actions. Real
linearity of the ambient actions gives integer linearity of the
restrictions.

`fullLogLatticeAssemble_equivariant` states

\[
A(g\cdot y,z)=g\cdot A(y,z).
\]

The proof evaluates the two underlying vectors and uses the fact that
arithmetic permutations fix constant vectors. Finally,
`fullLogIntegralSplit_equivariant` states

\[
S(g\cdot x)=(g\cdot (Sx)_1,(Sx)_2).
\]

Its first component follows from equivariance of the centered projection;
its second follows from invariance of the mean and injectivity of
`ℤ → ℝ`. Thus the scalar factor is exactly the ordinary integers with
trivial arithmetic action. Fields with one infinite place are included.

## Provenance and scope

Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, proof
of Proposition 3.1, printed p.209 (PDF p.218), uses the invariant
lattice `M = M₀ + ℤe` and its unit-lattice and trivial-integer factors
in the Herbrand-quotient calculation. Registered source:
`milne-2020-class-field-theory`, SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.

The explicit integer linear equivalence and restricted automorphism
homomorphisms are internal adapters of that decomposition, specialized
to all infinite places. Their derivation uses the imported mean
splitting, exact augmented-lattice membership, and arithmetic
invariance. This module supplies no quotient action on units modulo
torsion, categorical representation isomorphism, cohomology comparison,
or Herbrand-quotient formula; these remain subsequent steps.
