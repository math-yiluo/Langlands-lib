# Direct levels on selected finite-etale orbit covers

This internal unit proves that full source-point stabilizer fixedness is
automatic for actual restricted direct levels. It consequently simplifies
the published selected-cover range equivalence to target-orbit membership
alone and carries its level-arrow naturality to that simpler subtype.

The parameters retain the actual universe-zero number fields, central simple
unitary algebra, Harris signature charts, abelian family, supplied dual
witness and dual-valued map, integral-order action, tensor and duality
prerequisites, Weil-transition and adelic comparisons, and torsion
finite-etaleness prerequisite. The original test scheme is quasi-separated;
finite geometric fibres, invertible torsion orders and finite-etale roots
of unity remain supplied. The frame right action, commuting monodromy action,
raw right-orbit quotients and opposite right-action convention are unchanged.
Write `Gamma` for the actual `FundamentalGroup s hs`.

`harrisIntegralCMCoverRestrictionRawClass_stabilizer_fixed` applies to every
actual finite-etale cover `Y` of the original test scheme and every lift
`x : Fiber s Y`. Put `Tq = Over.mk (Y.obj.hom ≫ T.hom)` and let
`fq : Tq ⟶ T` have underlying morphism `Y.obj.hom`. On this direct source
family the integral action is literally `(relativeEndRestrict B fq).comp a`.
Quasi-separatedness of `Tq.left`, finite geometric fibres at `x.left`,
invertible torsion orders and finite-etale roots of unity there are explicit
inputs. For any original level `Z` and any direct fixed level `l` on this
family, the theorem proves that its actual restriction evaluation is fixed
by every `g : Gamma` fixing `x`. This general lemma does not require
connectedness or local noetherianity of the original test scheme, or
algebraic closure of the point field.

The proof uses the published
`harrisIntegralCMRestrictionImageFixedEquivAt` for this actual source and
point. Its value at `l` is fixed under the image of every element of the
actual source fundamental group. Apply this fixedness to
`stabilizerLift s hs Y x ht g hg`, using the supplied equality
`hg : g • x = x`. The published equation
`fundamentalGroupMap_stabilizerLift` identifies the actual image of this
lift with `g`. Finally, the image-fixed equivalence's underlying-value
formula identifies its value with the stated restriction evaluation.
Thus the conclusion concerns the full point stabilizer, using the actual
fundamental-group map.

For the selected-cover constructions, the original test scheme is also
connected and locally noetherian, the point field is algebraically closed,
and the original raw fixed-level set at `U` is nonempty. Fix original
Harris levels `U`, `V`, `Z`, a raw class `q` at `V` and a raw class `r`
at `Z`. Now `Y` is the existing selected finite-etale orbit cover of `q`
and `x` its distinguished lift. The same explicit prerequisites on `Tq`
and `x.left` are retained.

`harrisIntegralCMFiniteOrbitCoverHomLevelEquiv` is an equivalence between
actual cover morphisms from `Y` to the selected cover of `r` and the subtype
of direct fixed levels at `Z` whose actual restriction evaluation belongs
to `MulAction.orbit Gamma r`. This is an explicit target-orbit condition.
There is no additional stabilizer condition in this subtype. The definition
composes the published `HomLevelRangeEquiv` with the equivalence forgetting
its full-stabilizer clause. The inverse reinstates that clause using the
general fixedness lemma above. Both inverse laws for this last equivalence
are subtype extensionality.

`harrisIntegralCMFiniteOrbitCoverHomLevelEquiv_apply_val` proves that the
underlying value of the new equivalence is exactly the original `HomLevel`
of the actual cover morphism. The equality is definitional: simplifying the
range predicate does not change the forward direct level or its family.

For an original level arrow `j : Z ⟶ J`, choose a raw class `t` at `J`
and an equation that the existing right-orbit translation of `j` sends
`r` to `t`. `harrisIntegralCMFiniteOrbitCoverHomLevelMap` maps from the
direct-level subtype with orbit condition at `r` to the corresponding
subtype at `t`, on the same direct source family. It applies the inverse
new equivalence at `r`, postcomposes the resulting actual cover morphism
with the existing actual transporter of `j`, and applies the new
equivalence at `t`.

`harrisIntegralCMFiniteOrbitCoverHomLevelMap_val` proves that this map's
underlying direct level is the original direct raw tower map of `j`
on the underlying input level. Unfolding the definition gives the original
`HomLevel` of the reconstructed cover morphism followed by the transporter.
The published arbitrary-morphism theorem
`harrisIntegralCMFiniteOrbitCoverHomLevel_postcomp_transport` rewrites this
as the original tower map applied to the reconstructed `HomLevel`. Projecting
the source equivalence's `apply_symm_apply` law to underlying values
identifies that level with the input. This also proves that the original
tower transition preserves the target-orbit condition.

`harrisIntegralCMFiniteOrbitCoverHomLevelEquiv_natural` proves equality in
the target subtype between applying the source equivalence and then
`HomLevelMap`, and postcomposing the original cover morphism by the actual
transporter and then applying the target equivalence. After unfolding the
map, the source equivalence's `symm_apply_apply` law gives the equality.
Together with the underlying-value formula this is level-arrow naturality
for the original direct tower transition.

All constructions are internal deductions from the published actual
restriction, image-fixed, cover-stabilizer lifting, selected-cover range
and transporter constructions. This unit asserts no additional
original-literature result. The equivalence is for direct levels on
selected finite-etale covers of the supplied family. Extending the
comparison to the full admissible test category, comparing normalized
rational-isogeny classes, constructing an actual representing PEL scheme,
and proving its admissibility, smoothness and division-case projectivity
remain separate obligations of the full representability target.
