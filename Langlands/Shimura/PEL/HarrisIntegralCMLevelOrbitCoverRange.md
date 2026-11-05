# Exact image of the actual orbit-cover Hom-to-level comparison

This internal unit gives an exact range for the existing construction of direct
raw levels from actual finite-etale orbit-cover morphisms. It uses the original
universe-zero number fields, central simple unitary algebra, Harris signature
charts, abelian family, supplied dual witness and dual-valued map, and full
integral-order action. The tensor/duality, Weil-transition, adelic and torsion
finite-etaleness prerequisites remain supplied. The original test scheme is
connected, quasi-separated and locally noetherian, and its geometric point has
algebraically closed field. Finite geometric fibres, invertible torsion orders
and finite-etale roots of unity are explicit inputs. The old fixed-level set at
`U` is required to be nonempty. All groups, actions, raw orbit quotients and
selected covers are the existing actual constructions.

`harrisIntegralCMFiniteOrbitCoverHomEvaluationEquiv` applies to any finite-etale
source cover `Y`, an actual geometric lift `x` over the original point, and a
supplied pretransitivity instance for the actual fundamental-group action on
that source fibre. It identifies actual morphisms from `Y` to the selected
cover of a target raw class `q` with raw classes `z` satisfying both conditions:

- `z` belongs to the actual monodromy orbit of `q`;
- every element of the original fundamental group fixing `x` also fixes `z`.

The forward map is literal evaluation of the existing `HomRawMap` at `x`.
Target orbit membership comes from the actual fibre comparison; stabilizer
fixedness follows from equivariance. For injectivity, evaluation on the
pretransitive source determines the full raw-valued equivariant map, and the
existing `HomRawMap` injection determines the cover morphism. For
surjectivity, the existing transitive evaluation equivalence extends the
supplied value, viewed in the target orbit subtype, to an equivariant map.
The existing actual cover Hom universal property realizes that map by a cover
morphism. Its evaluation formula and the evaluation equivalence's inverse law
recover the prescribed value. This is a construction of an equivalence, not
an extra assumption that the point stabilizer is a fundamental-group image.

`harrisIntegralCMFiniteOrbitCoverHomEvaluationEquiv_apply_val` records that the
underlying raw value is exactly the target fibre comparison applied to
`x ≫ f.hom`, for the actual source lift and actual cover morphism `f`.

`harrisIntegralCMFiniteOrbitCoverHomLevelRangeEquiv` specializes to the selected
source cover of a raw class `q` at `V`, its distinguished lift `x`, and the
selected target cover of a raw class `r` at `Z`. Write
`Tq = Over.mk (Y.obj.hom ≫ T.hom)` and let `fq : Tq ⟶ T` have underlying
morphism `Y.obj.hom`. The direct restricted original family has integral
action literally `(relativeEndRestrict B fq).comp a`. Quasi-separatedness of
`Tq.left`, finite fibres at `x.left`, invertible torsion orders and finite-etale
roots of unity there remain explicit inputs.

The equivalence identifies actual morphisms between these selected covers
with the subtype of direct raw fixed levels at `Z` whose existing actual
restriction evaluation belongs to the target monodromy orbit and is fixed by
the full stabilizer of `x`. Its forward map is the original `HomLevel`, with
no change of family or action. Pretransitivity of this selected source fibre
is proved by the earlier actual orbit-cover comparison and is not an extra
caller premise. The existing `HomLevel_val` theorem places its value in the
stated subtype. Existing Hom-level injectivity proves injectivity. For
surjectivity onto this subtype, the new evaluation equivalence realizes the
evaluated raw class by an actual cover morphism, and injectivity of actual
restriction evaluation identifies its constructed direct level with the
supplied level. Both inverse laws are supplied by the constructed `Equiv`.
`harrisIntegralCMFiniteOrbitCoverHomLevelRangeEquiv_apply_val` explicitly
identifies the underlying forward map with the original `HomLevel`.

The full stabilizer condition is retained in both equivalences. In particular,
this unit proves no equality between that stabilizer and the image of the
source fundamental group, and does not identify all orbit-valued direct levels
with cover morphisms without this condition. Removing it still requires the
generic stabilizer-lift result. Comparison on the full admissible test
category, normalized rational-isogeny comparison, existence of the representing
PEL scheme, output admissibility, smoothness and division-case projectivity
remain open. The unit is an internal deduction from the unchanged transitive
evaluation, cover Hom universal property and direct restriction constructions;
it introduces no new original-literature assertion.
