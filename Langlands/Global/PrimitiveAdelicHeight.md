# Normalized heights of actual primitive adelic vectors

The module constructs a positive coordinate height on primitive vectors over the
actual full adele ring of any number field `F : Type u`. It uses the existing
`Adeles F`, `AdelicGL F n`, local completions and projection maps. No replacement
adelic carrier or topology is introduced.

The source is T. A. Springer, *Reduction theory over global fields* (1994), §1.8,
printed pp.209–210, definition of a primitive vector and equation (2), with its
scaling property (a). The source is registered as
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
The retained original is
`literature/Reduction theory over global fields (Springer, 1994).pdf`.

## Objects and normalization

`Vector F n` is `Fin n → Adeles F`. The map `rational` applies the principal
field-to-adele map to each coordinate. `IsPrimitive` says that an actual
invertible adelic matrix sends a nonzero principal rational vector to the given
vector. This is equivalent, by taking the inverse matrix, to Springer's condition
that an invertible adelic matrix sends the given vector to a nonzero rational
vector.

`finiteNorm` and `infiniteNorm` use the maximum coordinate norm in the actual
finite product of local completions. The definition `height` is

\[
 H(x)=\left(\prod_{v\mid\infty}\max_i\lVert x_{i,v}\rVert^{m_v}\right)
       \left(\prod_{v\nmid\infty}\max_i\lVert x_{i,v}\rVert\right),
\]

where `m_v = v.mult` is one at a real place and two at a complex place. The
finite-place completion norms are the existing normalized norms. Thus scaling
uses the existing normalized idelic absolute value, with the complex-place
multiplicity retained. This chooses maximum coordinate norms at all places;
it does not choose the Euclidean archimedean norm used later for Gauss's
rank-two estimate in Springer §1.9.

The real-valued formula is defined on ambient vectors. Its interpretation as a
positive height here is restricted to `IsPrimitive` vectors. `positiveHeight`
is that formula packaged as `ℝ≥0ˣ`, and `positiveHeight_val` proves that its
real value is exactly `height`. Dimension zero is allowed, but it has no
primitive vector under the displayed definition.

## Implemented supporting proofs

`IsPrimitive.exists_row` constructs an adelic row whose scalar product with the
vector is one. It chooses a nonzero rational coordinate, applies its inverse,
and uses the inverse adelic matrix. This construction is an internal proof step.

At almost every finite place both the row and the vector have integral
coordinates. Integrality bounds the vector norm above by one. Evaluating the
scalar-product identity and applying the ultrametric inequality bounds it below
by one. Consequently `eventually_finiteNorm_eq_one` and `hasFiniteMulSupport`
show that the finite product in the height formula is an actual finite product
on primitive vectors. Evaluating the same identity at any finite or infinite
place proves that the local vector is nonzero. These local positivity results
prove `height_pos` and justify `positiveHeight`.

`finiteNorm_smul` and `infiniteNorm_smul` follow from the local norm-scaling law.
Finite support for both the primitive-vector norms and the finite idele norms
permits distributing their finite products. This proves
`IsPrimitive.height_smul`: scaling by an actual idele multiplies height by
`IdeleAbsoluteValue.full F` of that idele. The existing product formula then
proves `height_diagonal_smul` for every nonzero principal scalar.

## Scope

This unit proves the displayed construction, finite-support, positivity and
scaling assertions. It does not prove compactness of normalized vectors,
comparison under arbitrary invertible adelic matrices, existence of rational
height minima, Gauss reduction, rank induction or Galois descent. In particular,
actual connected reductive Siegel coverage, algebraic setup existence and the
compatible compact subgroup remain obligations of the reduction task.
