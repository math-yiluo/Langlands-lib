# Statement: smoothness of the finite-Galois torus norm

Worker 1642. `Langlands.GroupScheme.GaloisNormSmoothnessStatement.{u}` is a
`Prop`-valued definition of the smoothness assertion for the actual norm
constructed in `Langlands.GroupScheme.Torus.GaloisNorm`. This module supplies
the statement for a separate proof task.

For fields `k,L : Type u` in an arbitrary common universe, assume
`Algebra k L`, `FiniteDimensional k L`, and `IsGalois k L`. Let
`T : CommGroupScheme (Spec (CommRingCat.of k))` have affine underlying
scheme, and write
`T_L := GaloisPointComparison.baseChanged k L T.toGrp`.
The statement also quantifies over the instances
`IsAffine T_L.X.left` and `LocallyOfFiniteType T_L.X.hom` required by the
existing affine Weil restriction. Its hypothesis and conclusion are exactly

```lean
IsSplitTorus (GaloisPointComparison.baseChanged k L T.toGrp) →
  Smooth (GaloisNorm.norm k L T).hom.hom.left
```

Here `IsSplitTorus` means existence of a group-scheme isomorphism to a finite
product of the actual multiplicative group over `Spec L`, including the
empty product. The norm has source `AffineWeil.groupScheme k L T_L` and
target `T.toGrp`. Its displayed underlying scheme morphism is the one whose
smoothness is asserted. The norm's existing all-algebra point formula uses
`AffineWeil.pointsEquiv`, the actual scheme-base-change comparison, and
`TensorGaloisPoint.norm`.

There are no valuation, Henselian, completeness, characteristic-zero, or
degree-invertibility hypotheses. Smoothness of the norm or of the original
group is not a premise. The statement asks only for smoothness of this
scheme morphism; it contains no surjectivity or rational-point openness
conclusion.

## Source and derived formulation

The motivating original is Tasho Kaletha and Gopal Prasad, *Bruhat–Tits
Theory: A New Approach*, Cambridge University Press, 2023, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. The proof of Lemma 2.5.12,
printed pp.89–90, one-based PDF pp.120–121, identifies the rational norm
with the map on `K`-points of the algebraic norm
`Res_{L/K}(T_L) → T` and uses smoothness and surjectivity of that morphism.
The original lemma concerns an open norm image and independence of the
splitting extension in the book's valued-field setting.

The authors' *Corrections and additions*, version of 1 November 2024,
registered as `kaletha-prasad-2024-corrections`, were checked at PDF
pp.24–25, Section 2.5. They correct the Serre reference in Remark 2.5.11
from Section 7 to Section 6 and replace the example in Remark 2.5.15.
They do not alter the algebraic-norm smoothness assertion used in the
proof of Lemma 2.5.12.

This statement extracts and generalizes that algebraic assertion to
arbitrary fields; it is derived infrastructure, rather than a literal
translation of the arithmetic lemma. The intended algebraic justification
is to base change to `L`, identify the Weil restriction with the product
indexed by `Gal(L/k)`, and identify the norm with multiplication on those
copies of `T_L`. A split torus is smooth, and multiplication on a finite
product of a smooth group is isomorphic, by a shear isomorphism, to a
projection. Smoothness then descends along the faithfully flat field
extension. This route also applies when the characteristic divides
`[L:k]`. It explains the generality and provenance of the target, without
claiming that these steps are proved in this statement module.
