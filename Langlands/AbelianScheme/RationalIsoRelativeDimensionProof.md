# Relative dimension under rational isomorphism of abelian schemes

Author: Worker 2954.

`Langlands.AbelianScheme.rationalIsoRelativeDimension` proves exactly the published
proposition `Langlands.AbelianScheme.RationalIsoRelativeDimensionStatement.{u}`.
For every base scheme `S`, abelian schemes `B`, `B'` over `S`, actual isomorphism
between their images in the rational category, and natural number `g`, it proves
`B.HasRelativeDimension g ↔ B'.HasRelativeDimension g`. The conclusion uses
Mathlib's `SmoothOfRelativeDimension` for the actual structure morphisms.
The theorem has no additional outer premise.

The proof clears integral denominators with the published
`Langlands.Rationalization.integralIsoData`, compares relative dimensions on
residue-field fibres, and recovers the affine-chart predicate on the original
base. The published `Langlands.GroupScheme.fieldMultiplicationIsogeny` supplies
positive multiplication isogenies over every field, including characteristic
dividing the multiplier. Only its finiteness component is needed here.

## Implemented proof

### Over a field

`relDim_unique_of_field`: let `q : Y ⟶ Spec K` be smooth of relative dimension `m` and
also of relative dimension `g`, with `Y` nonempty. Then `m = g`. The morphism is locally
of finite type, so `Y` is a Jacobson space by `LocallyOfFiniteType.jacobsonSpace`, and
`nonempty_inter_closedPoints` gives a closed point `y`. The published
`fieldSmoothClosedPointStalkDimension` says the stalk at `y` has Krull dimension `m`,
and also `g`.

`relDim_le_of_locallyQuasiFinite`: let `p : X ⟶ Spec K` be proper and smooth of relative
dimension `a`, let `q : Y ⟶ Spec K` be separated and smooth of relative dimension `b`,
let `φ : X ⟶ Y` be locally quasi-finite with `φ ≫ q = p`, and let `X` be nonempty. Then
`a ≤ b`. Choose a closed point `x` of `X` as above. `IsProper.of_comp` makes `φ`
proper, hence a closed map, so `φ x` is a closed point of `Y`. The published
`quasiFiniteAtStalkDimension` bounds the stalk dimension at `x` by the stalk dimension
at `φ x`. By `fieldSmoothClosedPointStalkDimension`, these are `a` and `b`.

### From residue-field fibres to Mathlib's chart predicate

`smoothOfRelativeDimension_resLE`: if an affine chart `f.appLE U V e` is standard smooth
of relative dimension `m`, then `f.resLE U V e` is `SmoothOfRelativeDimension m`. The
argument follows Mathlib's `HasRingHomProperty.iff_exists_appLE_locally`:
`HasRingHomProperty.iff_of_isAffine`, the arrow isomorphism `arrowResLEAppIso`, and
`RingHom.locally_of`.

`relDim_eq_of_open`: let `V` be an open of `X` containing `x`, with `V.ι ≫ f` of relative
dimension `m`, and let the residue-field fibre `pullback.snd f ι` over `s = f x` be of
relative dimension `g`, where `ι = S.fromSpecResidueField s`. Then `m = g`. Let
`W = pullback V.ι (pullback.fst f ι)`. Its morphism to `Spec κ(s)`,
`pullback.snd ≫ pullback.snd`, has relative dimension `0 + g`, because base change of an
open immersion is an open immersion. Through `pullbackRightPullbackFstIso`, the same
morphism equals the isomorphism to `pullback (V.ι ≫ f) ι` followed by its second
projection. That projection is a base change of `V.ι ≫ f`, so the composite has relative
dimension `0 + m`. `W` is nonempty: `Scheme.Pullback.range_fst` and
`Scheme.range_fromSpecResidueField` give a point of the fibre over `x`, and
`Scheme.Pullback.exists_preimage_pullback` lifts it to `W`. `relDim_unique_of_field`
then gives `m = g`.

`smoothOfRelativeDimension_of_fibres`: let `f : X ⟶ S` be smooth, and let every fibre
`pullback.snd f (S.fromSpecResidueField s)` be `SmoothOfRelativeDimension g`. Then `f`
is `SmoothOfRelativeDimension g`. The proof unfolds Mathlib's chart definition
(`smoothOfRelativeDimension_iff`). At each `x`, `Smooth.exists_isStandardSmooth` gives an
affine chart. A submersive presentation of that chart makes it standard smooth of
relative dimension `m = P.dimension`. The two previous lemmas and
`Scheme.Hom.resLE_comp_ι` give `m = g`. The same chart then witnesses relative
dimension `g` at `x`.

### Abelian schemes

`exists_positive_integral_inverse`: apply the published `integralIsoData` to the
actual rational isomorphism. It supplies integral maps `f`, `h` with both composites
equal to `m • 𝟙`, where `m` is the product of two nonzero integer denominators.
This published result clears both the rational denominators and the integral
torsion discrepancies in the two composite identities; no torsion-freeness of
integral Hom groups is assumed. Replace `h` by `m.sign • h`. Bilinearity of
composition makes both composites `(m.sign * m) • 𝟙`. The integer identity
`Int.sign_mul_self_eq_natAbs` makes this `m.natAbs • 𝟙`, and `m.natAbs` is a
positive natural number because `m ≠ 0`.

`groupHom_nsmul_id`: in the additive Hom group of an abelian scheme, `n • 𝟙 B` is the
published `multiplication B.toGrp n`. Additive notation is `Additive` of the pointwise
group, and `multiplication G n = (𝟙 G) ^ n`. `hom_baseChange_nsmul_id` combines this
with the published `multiplication_baseChange`: the base change of `n • 𝟙 B` has
underlying scheme morphism multiplication by `n` on the base-changed abelian scheme.

`hasRelativeDimension_of_integral`: from `f ≫ h = n • 𝟙 B`, `h ≫ f = n • 𝟙 B'`,
`0 < n`, `hmul` and `B.HasRelativeDimension g`, it derives
`B'.HasRelativeDimension g`. By `smoothOfRelativeDimension_of_fibres` it suffices to
treat each residue-field fibre. Fix `s`, let `j = S.fromSpecResidueField s`, and let
`A`, `A'` be the base changes of `B`, `B'` along `j`.

1. `A` has relative dimension `g` by the published `hasRelativeDimension_baseChange`.
2. `A'.X.left` is connected by `GeometricallyConnected.connectedSpace_of_subsingleton`.
   The published `smoothConnectedRelativeDimension` then gives some relative dimension
   `d` for `A'`.
3. `hmul` makes multiplication by `n` on `A` and on `A'` finite, hence locally
   quasi-finite. The base changes of `f ≫ h` and `h ≫ f` are these multiplications,
   so `LocallyQuasiFinite.of_comp` makes the base changes of `f` and of `h` locally
   quasi-finite.
4. `A` and `A'` are nonempty, since a geometrically connected morphism is surjective
   onto the nonempty `Spec κ(s)`. Both are proper and separated over `Spec κ(s)`.
   `relDim_le_of_locallyQuasiFinite`, applied to the base change of `f` and to the
   base change of `h`, gives `g ≤ d` and `d ≤ g`.

`rationalIsoRelativeDimension_of` applies `exists_positive_integral_inverse` and then
`hasRelativeDimension_of_integral` in both directions, with `f` and `h` swapped.
The final theorem `Langlands.AbelianScheme.rationalIsoRelativeDimension` applies this
reduction to the published unconditional `GroupScheme.fieldMultiplicationIsogeny`,
so its type is the exact target without the intermediate `hmul` premise.
Denominators are cleared over the original base before taking fibres. The proof
therefore uses ordinary base change of the integral maps and its preservation of
composition; it does not require constructing another rational base-change functor.
The existing `RationalBaseChange` construction remains available unchanged.

All arguments retain arbitrary universe and base scheme. On an empty base the
fibre criterion has no points to check. The proof transports each supplied `g`
and does not assert that the original abelian scheme has some globally constant
relative dimension.

## Dependencies

Published Library results used by Lean name:
`Langlands.Rationalization.integralIsoData`,
`Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension`,
`Langlands.AlgebraicGeometry.quasiFiniteAtStalkDimension`,
`Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension`,
`Langlands.AbelianScheme.hasRelativeDimension_baseChange` and
`Langlands.GroupScheme.multiplication_baseChange`, together with
`Langlands.GroupScheme.fieldMultiplicationIsogeny`. The last theorem proves
`Langlands.GroupScheme.FieldMultiplicationIsogenyStatement` without extra hypotheses.
Mathlib supplies the chart
predicate `SmoothOfRelativeDimension`, Jacobson spaces of schemes locally of finite type
over a field, properness and quasi-finiteness API, and pullback pasting.

## Provenance

The reduction to residue-field fibres and to an integral isogeny relation follows the
route in the task contract. The field comparison corresponds to Milne, *Abelian
Varieties* (1986, author revision 2022; registered as
`milne-abelian-varieties-1986-author-2022`), Section 8. Proposition 8.1 (printed/PDF
page 12) relates isogenies, equality of dimension, surjectivity and finite kernels.
Theorem 8.2 (page 13) shows that `n_A` is an isogeny for `n > 0`. Both were read in the
registered PDF. The retained errata snapshot
(`milne-abelian-varieties-1986-errata-2026-10-25`) lists no correction to Section 8.

The implemented route differs from Milne's. Milne derives Proposition 8.1 from the
fibre-dimension theorem. This proof instead compares Krull dimensions of stalks at
closed points under a quasi-finite map, using two published Library results. The
fibrewise chart argument is an internal derived argument, not a quotation of a source
theorem.

The geometric comparisons and assembly are derived work by Worker 2954.
Denominator clearing and the field multiplication theorem are reused from the
published Library; their companions describe their proofs and authorship.
The target statement and its imported dependencies are unchanged. This proof
uses the published prerequisites without modifying their constructions.
