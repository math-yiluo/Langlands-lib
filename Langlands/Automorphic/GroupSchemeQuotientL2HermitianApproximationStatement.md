# Hermitian approximation of the original canonical quotient L2 action

`GroupSchemeQuotientL2HermitianApproximationStatement` asks for an
approximate identity acting on the existing positive-central quotient
`Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)`. The operator is
exactly the previously constructed `haarQuotientL2IntegratedAction` of
the original positive right pullback representation. The quotient,
canonical measure, null classes and inherited Hilbert geometry remain
those of the existing construction.

Write `μG` for Mathlib's canonical **left** Haar measure on the full
actual adelic group. Integration of the representation uses its inverse
measure `μG.inv`, a right Haar measure. The target asserts the existence
of one sequence of real functions `f n` with all the following properties:

- Each function is continuous, compactly supported and nonnegative,
  integrable against `μG.inv`, and has integral one.
- Its reciprocal modular symmetry is
  `f n a = (Measure.modularCharacter a⁻¹ : ℝ) * f n a⁻¹`.
- For every neighborhood of the identity, the topological supports
  eventually lie in that neighborhood.
- The actual original integrated operators with complex weights
  `a ↦ (f n a : ℂ)` are symmetric contractions and converge strongly
  to the identity on every vector of the original quotient L2 space.

All hypotheses of the original canonical quotient action remain
explicit: an arbitrary number field, an actual affine group scheme
locally of finite type, a supplied central split torus with a finite
splitting, injective finite-index character restriction, and right
invariance of the fixed norm-one Haar measure. The target does not
require reductivity, finite quotient volume, an assumed approximate
identity or continuity as additional input. Original quotient orbit
continuity is already constructed. Preservation of inner products
follows from its original linear isometries.

Provenance is an internal specialization of
`RightHaarHermitianApproximationStatement` to
`haarQuotientL2BoundedRightAction` with the actual canonical group Haar
measure. In particular, this target calls for no new functional model of
the representation. Its general right-Haar prerequisite and the exact
proof of this specialization require independent proof publication.
This statement itself asserts an unproved proposition.

The source motivation is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), section 3.2, printed pp. 81–82 (PDF pp. 97–98),
especially (3.8), and section 9.3, printed pp. 246–247 (PDF pp. 258–259).
Those passages and the complete registered October 2026 errata were
reread before freezing this target. The reciprocal modular factor
agrees with the right-Haar condition there. The present target uses
continuous compact weights on the **full adelic group**. The book uses
smooth compact weights on the split-centre quotient
`A_G \ G(A_F)`. Thus this is a qualified continuous precursor: it proves
neither smooth-vector density nor descent of the weights to that group
quotient. Compactness, trace estimates and spectral decomposition remain
separate obligations. No equality of left and right Haar is assumed.
