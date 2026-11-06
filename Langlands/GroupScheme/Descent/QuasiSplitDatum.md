# Effective descent of actual group-and-Borel data

This internal construction descends an actual connected reductive group
and a compatible geometric Borel over an algebraic extension of fields.
It works in an arbitrary common universe `u`, with no restriction on
characteristic, perfectness, or dimension. Its input consists of actual
Čech data and compatibility, or an ambient datum and equality of the
Borel's overlap images on every test scheme. A descent solution is constructed.

## Geometric Borel reflection

`IsGeometricBorelSubgroup.iso_comp` proves that source isomorphisms preserve
both the field-level Borel condition and its chosen algebraic-closure
pullback. `IsBorelSubgroup.of_baseChange_of_isIso` reflects the Borel property
along an isomorphism between spectra of algebraically closed fields: pull
back along the inverse base isomorphism and transport through the natural
double-pullback comparison.

For an algebraic extension `K/k`, the algebraic closure of `K` is also an
algebraic closure of `k`. Choose the resulting `k`-algebra equivalence of
algebraic closures. The actual pullback comparisons and their naturality
transport the Borel inclusion over the closure of `K` to a base change of
the inclusion over the closure of `k`. Reflection along the isomorphism of
closure spectra gives this latter Borel condition. The existing
`isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure` supplies the
ground-field Borel condition and geometric Borel predicate.

The resulting
`IsGeometricBorelSubgroup.of_baseChange_of_algebraicExtension` assumes an
affine ambient group and that the original inclusion is closed.

## Actual group-and-Borel solutions

For a morphism `p : S ⟶ Spec k`, group schemes `G B` over `S`, actual data
`D : Datum p G`, `E : Datum p B`, and an inclusion `i : B ⟶ G`,
`QuasiSplitSolution D E i` records:

- solutions `group : Solution D` and `borel : Solution E`;
- an actual ground-field map `inclusion : borel.obj ⟶ group.obj`;
- the recovery equation
  `(baseChange p).map inclusion ≫ group.iso.hom = borel.iso.hom ≫ i`;
- affineness of both descended underlying schemes, connected reductivity
  of the descended ambient group, and the geometric Borel property of
  the descended inclusion.

Each solution retains its actual pullback isomorphism and compatibility
with the original Čech datum. `QuasiSplitSolution.quasiSplit` packages the
recorded reductivity and the constructed Borel as `IsQuasiSplit group.obj`.

`Datum.quasiSplitSolution` constructs this record for
`p = Spec (algebraMap k K)` and an algebraic extension `K/k`. Its inputs
are `D`, `E`, connected reductivity of `G`,
`IsGeometricBorelSubgroup i`, and `Compatible E D i`. There is no
supplied ground-field model or effectiveness premise.

Reductivity makes `G` affine, and closedness of the Borel inclusion makes
`B` affine. The published `Datum.affineSolution` constructs actual affine
solutions `s` and `t`. The field-extension map is fpqc, so
`Solution.descendHom` constructs the descended inclusion `f`.
Its recovery square is `Solution.baseChange_descendHom`.
`IsConnectedReductive.of_fieldExtension` reflects reductivity from the
given group via `s.iso`.

The recovery square identifies the pullback of `f` with
`t.iso.hom ≫ i ≫ s.iso.inv`. Source and target Borel transport therefore
prove that this pullback is geometric Borel.
`IsClosedSubgroup.of_baseChange_of_isAffine` reflects closedness of `f`
using the constructed affine solutions. The algebraic-extension
reflection proved above then makes `f` geometric Borel over `k`.

## Construction from overlap image invariance

The selected definition `Datum.quasiSplitSolutionOfRangeEq` takes only
the ambient datum `D`, reductivity of `G`, the geometric Borel inclusion
`i`, and the equality

```text
range ((baseChange (fst p)).map i ≫ D.overlap.hom)
  = range ((baseChange (snd p)).map i).
```

These are actual represented subgroup ranges on all relative test schemes,
including nonreduced and nonaffine tests. The published `Datum.closedSubgroup`
constructs the Borel overlap isomorphism from this equality and proves its
cocycle by cancellation through the closed inclusion.
`Datum.compatible_closedSubgroup` proves compatibility of the inclusion.
Applying the preceding constructor returns both actual solutions, their
compatible pullback isomorphisms, the exact inclusion recovery equation,
and the proved geometric Borel and quasi-split properties.

## Provenance and scope

This is an internal derivation from the published algebraic-closure
comparison, actual pullback naturality, Borel transport and reflection,
affine group datum effectivity, compatible homomorphism descent, and
connected reductivity reflection APIs. No external structural theorem or
new axiom is introduced.

The ambient datum and its Borel invariance remain inputs. This unit does
not construct a pinned overlap, an inner action discrepancy, or a full-centre
adjoint quotient. It therefore supplies the effective group-and-Borel
descent step toward quasi-split inner-form existence; the unconditional
`QuasiSplitInnerFormExistenceStatement` remains open.
