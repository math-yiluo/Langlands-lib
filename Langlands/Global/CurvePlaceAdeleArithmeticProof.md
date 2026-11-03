# Faithfulness and coherence of actual curve-place adelic maps

`Langlands.Global.curvePlaceAdeleArithmetic` proves exactly
`Langlands.Global.CurvePlaceAdeleArithmeticStatement` in a common arbitrary
universe, with all four of its quantified conclusions and no added hypotheses.
The argument uses the actual curve-place completions and restricted product
already in the Library.

For the level diagonal, choose one place from the stated nonempty type. Equality
of two images implies equality in this one completion by evaluation. The
algebra map from the field into that completed field is injective, so the two
outside-`S` integers have equal underlying field elements and hence are equal.
The proof works for every finite `S`, including the empty set.

The additional helper
`injective_curvePlaceAdeleLevelDiagonal_of_functionField` obtains the nonempty
place type from the published `curvePlace_nonempty` for a function field. This
helper needs no perfectness assumption. The full-field diagonal, whose existing
construction does require perfect constants and the compatible finite
`RatFunc` presentation, is tested at the published `curvePlaceReference`.
This place lies above the rational-function place at zero. Injectivity of the
map into that completed field proves injectivity of the full diagonal without
an additional nonemptiness premise or separability premise.

For presentation coherence, the underlying place transports preserve identity
and composition by the definitions of valuation-subring comap and field
equivalence. The Lean lemmas `curvePlaceEquiv_refl_apply` and
`curvePlaceEquiv_trans_apply` are proved by reflexivity. The resulting local
completion source and target types are definitionally the same in the local
identity and composition comparisons; no extra identification is postulated.

The local completion transports are continuous by the published construction.
They agree with the original field equivalences on the algebra maps into the
completions by `curvePlaceCompletionCongr_algebraMap`. The image of the original
field is dense by Mathlib's `HeightOneSpectrum.denseRange_algebraMap`, and the
target completed field is Hausdorff. `DenseRange.equalizer` therefore identifies
the local identity transport with the identity and the transport along a
composite with the composite of the two local transports. These are equalities
of ring equivalences, proved by equality of their underlying functions.

Finally, `curvePlaceAdeleCongr_apply` expresses each transported adelic
coordinate by the corresponding local completion transport. In the identity
case, the local identity law gives every original coordinate back. In the
composition case, every target place has a source place under the transported
place equivalence, and the local composition law gives equality at that
coordinate. Restricted-product extensionality and ring-equivalence
extensionality finish both global laws.

Neither presentation law requires a nonempty place type, perfect constants,
or a finite rational-function presentation. In an empty place type, the
coordinatewise extensionality proofs still establish the two laws.

The final theorem supplies the four conjuncts in the statement's order. This
proof is derived arithmetic infrastructure motivated by the adelic levels in
Conrad, *Weil and Grothendieck approaches to adelic points*, December 31, 2011,
Section 2 opening, printed p.1. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Its proof route is the dense-field uniqueness
argument above; it does not claim that this coherence package is separately
stated in Conrad. Conventional global-place realization, local compactness,
diagonal discreteness, model descent, and geometric point-space comparisons
remain separate obligations.
