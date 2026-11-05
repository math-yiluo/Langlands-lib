# Normalized root-function pullback through an actual derived inclusion

Authors: Worker 27 and Worker 1631. The construction uses Worker 1631's
actual root-point transport and adapts the existing central-isogeny
root-family comparison to a derived inclusion.

Over a field `k : Type u`, let `d : D ⟶ G` be a supplied actual derived
inclusion, with `D` affine and locally of finite type and `G` affine and
smooth. Retain the supplied split tori `T`, `S`, `A`, maps `e : T ⟶ S`,
`c : A ⟶ S`, `j : T.toGrp ⟶ D`, `i : S.toGrp ⟶ G`, and square

`j ≫ d = CommGroupScheme.groupHom e ≫ i`.

The product of `e` and `c` is flat and surjective on schemes, and the
composite of `c` with `i` is central in `G`. These structural hypotheses
remain inputs. No isogeny or rational-point surjectivity is assumed for `e`.

The definition `RootFunctionFamily.derivedPullback` sends an arbitrary
ambient root-function family `φ` to a family on the derived group.
At a source character that is an actual root, it takes the inverse image
under the actual root bijection and evaluates `φ` at that ambient root
and `rationalPoints.map d g`. It sets the value to `⊤` if the source
character is not a root or if `g` lies outside its actual root group.
The theorem `derivedPullback_isNormalized` verifies exactly those two
normalization conventions.

The construction `derivedRootGroupPointsEquiv` specializes the all-test
root-point equivalence to rational points. Its forward map is the original
derived rational-point map, as proved by
`derivedRootGroupPointsEquiv_coe`. The evaluation lemmas
`derivedPullback_apply` and `derivedPullback_apply_root` show that pullback
preserves every value on corresponding actual root points.

The theorem `derivedPullback_vadd` proves that translation by `v : V T`
after pullback equals pullback after translation by the literal
`cocharacterMapReal e v`. On source root groups this follows from natural
evaluation and the actual root bijection; outside them both values are
`⊤`. The helper `IsNormalized.centralComplement_vadd` proves that the
central factor's real cocharacter image acts trivially on normalized
ambient families, since every ambient root vanishes on that factor.

The theorem `derivedPullback_injective` recovers a normalized ambient
family from its pullback. Every actual ambient root point has a preimage
under the original derived point map; its value is recovered by the
evaluation lemma. All remaining ambient values are fixed by normalization.

The theorem `equipollent_derivedPullback_iff` preserves and reflects the
original equipollence relation on normalized families. One direction uses
translation compatibility and injectivity. For the other, decompose an
ambient real translation as a retained-torus image plus a central-factor
image, using `DerivedTranslation`; the latter acts trivially, and the
former pulls back to the source translation. Thus this argument includes
ambient central directions without requiring surjectivity of the
retained-torus map.

Finally, `rootFiltration_derivedPullback_iff` identifies membership in each
original source filtration with membership of the literal image point in
the corresponding ambient filtration, while retaining source root-group
membership. Surjectivity of the actual root-point equivalence gives the
exact image equality `image_rootFiltration_derivedPullback`.

This is an internal construction from the actual derived root and
root-point bijections, original real translations, and their central-factor
decomposition. The full valuation axioms, split-torus and full-centralizer
compatibility, source-apartment construction, and final normalizer-image
theorem are separate obligations.

`IsNormalized.vadd_eq_self_of_mem_rootAnnihilator` additionally states
triviality of translation by every vector in the common root kernel,
without restricting that vector to the central-factor image. Its proof
uses vanishing of root evaluations and normalization away from roots.
The central-factor helper and the existing pullback construction remain
available with their original meanings.
