# Classes of rectangles and unitary blocks

Author: Worker 5121. Module `Langlands.Representation.Classification.TadicBlockBlocks`,
namespace `Langlands.Classification.TadicBlockBlocks`. Helper module of the proofs of
`Langlands.Classification.TadicBlockReductionFromInputs` and
`Langlands.Classification.TadicBlockReduction`. Throughout, `hA` is
`BernsteinUnitaryProductIrreducibility` (Tadić 1986, Theorem 2.5(i)), `hC` is
`ComplementarySeriesOpenIntervalUnitarity` (the open-interval clause of Proposition 2.9) and
`hD` is `UnlinkedSocleProductIrreducibility` (Zelevinsky 1980, Proposition 8.5).

## Classes of socles

`cls_eq_of_isZelevinskySocle`: Zelevinsky socles of one multisegment have the same class,
in any presented rank (their ranks equal the degree; published
`nonempty_iso_of_isZelevinskySocle`). `rectSocle q` is a chosen socle of `q.rect` and
`rectCls q` its class `[⟨a(n,d)^(ν^α ρ)⟩]`. `one_le_coeff_prod_rectCls` (Zelevinsky 8.4 for
rectangles, from `TadicBlockRing.one_le_coeff_basisClass_mul`) and
`isZelevinskySocle_of_cls_eq_prod_rectCls`: an irreducible representation with class
`∏_{q ∈ J} [⟨rect q⟩]` is a Zelevinsky socle of `∑_{q ∈ J} rect q`.

## Complementary products

`tadicMultisegment_twist`: `ν^β a(n,d)^ρ = a(n,d)^(ν^β ρ)`. `not_isLinked_twist_pair`: for
`0 < |β| < 1/2`, segments of `a(n,d)^(ν^β ρ)` and `a(n,d)^(ν^(-β) ρ)` are never linked
(linked segments have beginnings differing by an integral twist, which would force
`2β ∈ ℤ`). For a unitarizable socle `σ` of `a(n,d)^ρ` and `|β| < 1/2`:
`tadicComplementaryProduct_isIrreducible` — for `β = 0` by
`BernsteinUnitaryProductIrreducibility`, otherwise by `UnlinkedSocleProductIrreducibility`
(the blocks `ν^{±β} σ` are socles of the twisted rectangles by the published real-twist
compatibility); `tadicComplementaryProduct_isUnitarizable` — by the open-interval clause of
Proposition 2.9, `ComplementarySeriesOpenIntervalUnitarity` (module
`TadicComplementarySeriesOpenIntervalStatement`), with `α₀ = 1/2`, the irreducibility on
`(-1/2, 1/2)` being the previous result; the endpoint clause of 2.9 is not used.
`cls_tadicComplementaryProduct` and `cls_segmentFactor_eq_rectCls`: its class
is `[⟨a(n,d)^(ν^β ρ)⟩][⟨a(n,d)^(ν^(-β) ρ)⟩]`.

## Blocks and their products

`UIrr F T`: an irreducible unitarizable representation of some `GL_N`, `N > 0`, with class
`cl`. `listShape` and `listProduct`: the block shape and normalized product of a list of
blocks of total rank `n`; `listProduct_irr_unit` (Bernstein 2.5(i)) and `cls_listProduct`
(class is the product of classes, from `TadicBlockRing.cls_product`).

`BaseUnitary q`: every socle of `a(n,d)^ρ` is unitarizable. `zeroBlk` is `⟨rect q⟩` for
`α = 0`, `pairBlk` (taking `hA`, `hC`, `hD`) the complementary product `ν^α σ × ν^(-α) σ`
with `σ` a chosen socle of `a(n,d)^ρ`, irreducible by `pairRep_irr` and unitarizable by
`pairRep_unit`; `zeroBlk_cl`, `pairBlk_cl` give their classes. `UFamily J`: admissible,
reflection invariant and base unitary. `split_family`:
`J = (α = 0 part) + (α > 0 part) + (α > 0 part).map refl`. `famBlocks J` lists the blocks of
the `α = 0` part and of the positive part; `famBlocks_cl` (product of classes is
`∏_J [⟨rect q⟩]`), `famBlocks_N` (total rank is the degree of `∑_J rect q`) and
`famBlocks_isTadicXBlock` (they are members of `X_k` once all base degrees are at most `k`).

`isTadicXBlock_analysis`: under `(U^k)` (`TadicSocleUnitarity k`), `hA` and `hD`, a member of
`X_k` is irreducible and its class is `∏_J [⟨rect q⟩]` for a unitary family `J` (one
parameter with `α = 0`, or the pair `±α`).

## Sources

Zelevinsky 1980, Propositions 8.4–8.5 (p.196); Tadić 1986, Theorem 2.5(i), Proposition 2.9
(p.350; only its open-interval clause) and the
definition of `X_(m-1)` in §4.6 (p.358) and Lemma 4.8 (p.360).
