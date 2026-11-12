# Multiplication pullback of symmetric line bundles over arbitrary fields

Author: Worker 537.

The theorem `Langlands.GroupScheme.fieldSymmetricMultiplicationPullback`
proves the exact published proposition
`Langlands.GroupScheme.FieldSymmetricMultiplicationPullbackStatement.{u}`.
The universe `u` is arbitrary. For every field `K : Type u`, every actual
commutative group scheme `G` over `Spec K` with smooth, proper and
geometrically connected structure morphism, and every actual line bundle
`L` on `G`, symmetry under pullback by `multiplication G (-1)` implies,
for every natural number `n` with `0 < n`, existence of an actual
module-sheaf isomorphism

\[
[n]^*L \cong L^{\otimes(n\cdot n)}.
\]

Here pullback means `AlgebraicGeometry.Scheme.Modules.pullback` along
`(multiplication G (n : ℤ)).hom.hom.left`, applied to `L.obj`.
The tensor power is exactly `Langlands.Scheme.Modules.tensorPow L.obj
(n * n)`: its factors are right-associated sheafified tensors and include
the final structure-sheaf unit. The conclusion is `Nonempty` of that
actual categorical isomorphism type.

## Implemented proof

This module applies the published theorem
`fieldSymmetricMultiplicationPullbackOfCube` to the published unconditional
theorem `fieldCubePullback.{u}`. This supplies the assembly's sole premise
and leaves the Library proposition itself as the final theorem's type.
All prerequisites are imported by Lean name.

The [multiplication assembly](FieldSymmetricMultiplicationPullbackAssembly.md)
proves tensor invertibility from the actual local rank-one property of
the line bundle and its pullbacks, using
`locallyFreeRankOneIffTensorInvertible`. It compares the explicit
sheafified tensor with the monoidal tensor by `localizedTensorIso`.
The Picard group used in its argument is constructed from actual tensor
invertible module sheaves modulo isomorphism.

Write `q(k)` for the Picard class of `[k]^*L` and `a` for the class of `L`.
The assembly trivializes `[0]^*L` by factoring the zero multiplication
through the identity section over the field and applying
`fieldLineBundleTriviality`. Pullback by the identity gives `q(1) = a`;
symmetry gives the class of `[-1]^*L` equal to `a`.
Specializing the balanced cube identity to the maps `[k+1]`, `[1]`
and `[-1]` gives

\[
q(k+2)+q(k)=q(k+1)+q(k+1)+(a+a).
\]

Induction keeping two consecutive values proves `q(k) = (k*k) • a`,
using `(k+2)^2+k^2=2(k+1)^2+2`. A separate induction identifies the class
of the exact concrete tensor power with `(k*k) • a`. Finally
`PicardGroup.ofObject_eq_iff` turns the class equality into existence of
the required actual module-sheaf isomorphism.

The [balanced cube proof](FieldCubePullbackProof.md) supplies the cube
identity unconditionally. It applies the published two-bundle geometric
cube theorem to the positive and negative balanced tensors on the triple
product, then pulls their comparison back along the three maps.
Its field-fibre triviality, local rank-one and pullback/tensor comparisons
are already proved in its imports. The new theorem therefore retains no
cube, square, descent, coherence, tensor-invertibility or Picard-action
premise. It adds no ampleness, projectivity or characteristic restriction;
the formula includes characteristic dividing `n`.

## Source and provenance

This is the final internal composition of the published balanced cube
proof with the published multiplication recurrence assembly. The
recurrence and all geometric and tensor constructions remain in their
existing modules; this module introduces only the final application.

The motivating source is J. S. Milne, *Abelian Varieties*, the 1986 chapter,
author corrected version dated January 2, 2022. Corollary 6.6 on printed
and one-based PDF p.9 explicitly gives the symmetric formula and derives
its recurrence from the preceding cube corollary. The implemented proof
follows that recurrence through actual Picard classes and then returns
to actual sheaf isomorphisms. The field presentation and exact scope are
explained in the
[published statement](FieldSymmetricMultiplicationPullbackStatement.md).

The source is registered as
`milne-abelian-varieties-1986-author-2022`, retained at
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`,
SHA256 `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The relevant p.9 passage and retained author errata were read. The
balanced cube proof documents the missing inverse in the printed
Corollary 6.5 and its use of the three inverse pair factors from
Corollary 6.4; the present final application uses that proved balanced
identity.
