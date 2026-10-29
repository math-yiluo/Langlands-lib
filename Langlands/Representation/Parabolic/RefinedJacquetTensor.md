# Upper normalized refined Jacquet modules of external tensor products

This internal construction compares actual quotient representations. Fix a
p-adic field F, its compatible topological data T, an ordered shape B, a
refinement S, and arbitrary complex representations A_i of GL_(B.size i)(F).
The field and carrier universes are independent. No smoothness, admissibility,
finite length, irreducibility, or positivity of a rank or a block family is
assumed beyond the existing block-shape definitions. Empty index families and
rank zero are included.

`Langlands.RefinedJacquetTensor.jacquetEquiv T B S A` is an actual
`Representation.Equiv` from the upper normalized refined Jacquet module of
`FiniteTensor.external (fun i => (A i).ρ)` to the external tensor product of
`T.normalizedJacquet (S i) (A i).ρ`, pulled back along the actual
`refinedLeviEquiv F.Carrier B S` inverse. Its pure tensor formula sends the
refined quotient class of `tprod v` to `tprod (fun i => (S i).jacquetMk (A i).ρ
(v i))`. The equivalence has an inverse and intertwines the full refined Levi.

The underlying linear equivalence uses the published generic untwisted
product-subgroup coinvariant equivalence
`RefinedOppositeJacquetTensor.coinvariantsEquiv`. Although its namespace is
historical, this generic lemma contains no opposite parabolic. The individual
upper parabolic quotient carriers differ from their ambient subgroup
coinvariants. Each is transported by the inverse of the published
`BlockShape.jacquetModuleEquiv`; `PiTensorProduct.congr` supplies their tensor
transport. The published formula `jacquetModuleEquiv_mk` gives the formula on
pure tensors.

The inverse first applies the tensor of `BlockShape.jacquetModuleEquiv` to
return to the ambient subgroup quotient carriers, then the inverse of the
generic product-coinvariant equivalence. That generic inverse is constructed
by descending the map `v ↦ [tprod v]` in every tensor slot: a relation in one
factor is killed by the corresponding element supported in that factor of
the product subgroup. The two compositions are proved to be identity on
quotient representatives and pure tensors in `Tensor.CharacterLocalization`.
The trivial-character relation transports preserve representatives. Thus the
inverse here sends a tensor of factor classes `[v_i]` back to the refined
class of `tprod v`; it is an actual inverse, including for the empty family.

Normalization is the inverse half of the upper modulus. The published
`T.refinedLeviHalfModulus_eq_prod` in `RefinedInductionTensorNormalization`
identifies the refined positive half with the product of the block positive
halves. Inverting gives `refinedLeviInverseHalfModulus_eq_prod`. On quotient
pure tensors, `normalizedRefinedJacquet_mk` and
`normalizedJacquet_mk_eq_inv_halfModulus` expose the two inverse-half actions.
Multilinearity extracts the product of block scalars; the product identity
and the actual refined Levi coordinates then give equivariance. Surjectivity
of the refined quotient map and tensor induction extend this identity to
every vector.

`normalizedRefinedJacquetCongr T B S e` separately descends any coarse-Levi
representation equivalence through the actual upper refined quotient. Its
two directions are the published quotient maps induced by e and its inverse.
Their compositions are identity on quotient representatives. Its `_mk`
formula preserves the given representative.

The construction adapts the published opposite tensor comparison of Worker
243, with the upper parabolic carrier transports and inverse-half
normalization supplied by Worker 485 in shared task draft revision 1.
Worker 1004 audited that complete draft, its carrier transports, inverse,
normalization and transitive dependencies, and prepared this publication.
It reuses published results by Lean name and asserts no original-source
theorem. It does not provide flattened transitivity or the segment-specific
Jacquet calculation.

The complete transitive project import closure has 71 modules including this
entry module. All 70 published dependency Lean/Markdown pairs agree byte for
byte with Library commit `89ea09c9820d69c341612113daf276cd4d51dbf8`, as
checked when preparing this contribution. The closure contains the underlying
field, block, representation, smoothness, admissibility, unitary, twist, tensor,
filtration, coinvariant, refinement and opposite quotient constructions,
elementary compatibility results and proposition definitions. The only
classification modules in the closure are
`Supercuspidal`, `SupercuspidalTwist` and
`CuspidalJacquetMultiplicityStatement`; the latter supplies the actual opposite
quotient carrier in the imported helper module and no multiplicity proof is
used. The construction uses the generic untwisted coinvariant comparison and
the refined Levi embedding identity from that module. It does not consume
its opposite normalized tensor comparison.

The closure contains none of the forward special square-integrability,
ordered conversion, square-integrable exhaustion, regular exhaustion,
square-integrable Langlands classification, strong-head analytic classification,
tempered-block uniqueness, multisegment exhaustion, ordered-head existence,
quotient coverage, segment-head product irreducibility, generic segment-product
uniqueness or multisegment socle exhaustion units, their proofs or their
mathematical conclusions. Neither a derivative formula nor Zelevinsky section
9.3 or 9.17 is used. These restrictions apply transitively to all dependencies.
The implementation instead constructs an equivalence on arbitrary modules by
coinvariant quotient algebra and verifies the given normalized actions.

The audit checks each of the task's exclusions against the complete closure:

| Excluded task | Excluded conclusion; audit result |
| --- | --- |
| `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | Forward special square-integrability: absent. |
| `8252833d-c269-41a9-824c-5879e531b23b` | Parent ordered conversion: absent. |
| `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | Square-integrable exhaustion: absent. |
| `bf433f0a-921a-428c-b0c0-6475438125ac` | Regular exhaustion: absent. |
| `1cb45da2-7007-4351-a694-594fb148b8d1` | Square-integrable Langlands classification: absent. |
| `aca8805b-054f-4d56-8045-12db7f623404` | Strong-head analytic classification: absent. |
| `52e97845-36bb-457d-b76f-70753334b88c` | Tempered block uniqueness: absent. |
| `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | Multisegment exhaustion: absent. |
| `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | Ordered strong-head existence: absent. |
| `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | Quotient coverage: absent. |
| `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Segment-head product irreducibility: absent. |
| `30341ae4-65f2-4a0e-9283-763db01a409e` | Generic segment-product uniqueness: absent. |
| `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Multisegment socle exhaustion: absent. |

Their mathematical conclusions, exact proof successors and downstream
consequences are not used. In particular, the three classification modules
listed above supply definitions, quotient constructions and elementary
twist or equivalence compatibilities, without invoking any of these excluded
conclusions. `RefinedInductionTensorNormalization` imports the tensor-induction
statement, but its product half-modulus identity follows directly from the
explicit modulus definition and monoid homomorphisms; it assumes no proof of
that statement.

The module's development `lean_check`
`96cf8b2e-ef87-4804-8a06-c95ebaddcdd0` succeeded without errors or warnings.
Declaration inspection of `Langlands.RefinedJacquetTensor.jacquetEquiv`
reported independent level parameters `uF,uV` and only `propext`,
`Classical.choice` and `Quot.sound`. A separate private full-signature check
`604995b1-0b37-4854-8f3b-4396f4a9c0dd` also succeeded: the unapplied main
constant has the complete requested telescope with no additional hypotheses,
and the congruence and pure tensor formula were inspected in full. The
congruence even permits different universes for its two carriers. The
tensor-induction extension uses a finite local heartbeat limit of 800000.
These are development checks; independent semantic review and publication
are separate requirements.
