# Ample line bundles on abelian schemes over normal finite-type `ℤ`-domains: proof

Author: Worker 5655 (Task 5655). The reduction it applies was written by
Worker 1318. The two-axis extension property comes from Task 5678 and the
generic-ampleness criterion from Task 5716.

`normalFiniteTypeAbelianAmpleExistence` proves the entire published
proposition `NormalFiniteTypeAbelianAmpleExistenceStatement.{u}` for an
arbitrary universe `u`. For every integrally closed commutative domain `R`
of finite type over `ℤ` and every Library abelian scheme `A` over `Spec R`,
the total space `A.X.left` has an ample line bundle.

## Implemented proof

The proof applies the published reduction
`normalFiniteTypeAbelianAmpleExistence_of_twoAxis_genericAmple` to two
published unconditional theorems:

1. `Langlands.AbelianScheme.normalFiniteTypeTwoAxisExtensionProperty`
   (module `Langlands.AlgebraicGeometry.Picard.NormalModelTwoAxisExtensionProof`,
   Task 5678), proving
   `Langlands.AbelianScheme.NormalFiniteTypeTwoAxisExtensionProperty.{u}`.
   Over a normal finite-type integer domain, every self-product line bundle
   on the generic fibre that is trivial on both unit axes extends to an
   actual line bundle on `A ×_{Spec R} A`, with an actual isomorphism
   between its generic restriction and the given bundle.
2. `noetherianAffineAbelianGenericAmple` (module
   `Langlands.AlgebraicGeometry.Picard.NoetherianAffineAbelianGenericAmpleProof`,
   Task 5716), proving `NoetherianAffineAbelianGenericAmpleStatement.{u}`. On an abelian scheme
   over a noetherian affine domain, a line bundle whose pullback to the
   generic fibre is ample is ample on the total space.

The reduction works as follows (see its own Markdown). The generic fibre `B`
of `A` has an ample bundle by the published field ample-existence theorem.
The field ample diagonal correspondence turns that bundle into a bundle `D`
on `B × B`. `D` is trivial on both unit axes and its diagonal restriction is
ample. Input 1 extends `D` to a bundle `E` on `A × A`. The pullback of `E`
along the diagonal of `A` is a total bundle with ample generic restriction.
Input 2 then makes it ample on `A.X.left`. A finite-type `ℤ`-algebra is
noetherian, so input 2 applies.

## Scope and dependencies

No hypothesis is added. The only argument used is the published reduction
applied to the two theorems, so the proof keeps every normal finite-type
integer domain and every actual abelian scheme.

Input 1 is proved through Murre's criterion. The class presheaf of line
bundles on `A ×_S A` trivial on both unit axes is representable over
noetherian affine bases, following Raynaud, LNM 119, Theorem III 4.4 (see the
Markdown of `NormalModelTwoAxisExtensionProof`).

No Lean file in the import closure of this module names
`NormalFiniteTypeAbelianPicardSheafAFSchemeStatement`,
`FiniteTypeAbelianPicardSheafSchemeStatement`,
`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` or
`SmoothFamilyAbelianRepresentabilityStatement`. So the proof uses neither
these statements nor their proofs. The closure also names none of
`RelativeDualSchemeExistenceStatement`, `FieldDualSchemeExistenceStatement`,
`FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement` and
`FiniteTypePicardStackAtlasStatement`, the targets of the paused allocations.

The mathematical source is Faltings–Chai, *Degeneration of Abelian
Varieties* (1990), Chapter I: the proof of Theorem 1.9 (printed p.6), which
shows global projectivity over an irreducible normal base, and Remark 1.10(a)
(printed p.7), which records it over any noetherian normal base. Input 2
rests on the closedness of the ample locus, Remark 1.10(b) (printed p.7).
The Lean route is the internal composition described above. It replaces the
dual abelian scheme and Poincaré bundle of the source with line bundles on
`A ×_S A` that are trivial on both unit axes.
