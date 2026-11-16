# Closed fibres of a reductive open subgroup with the same generic fibre

This is an internal construction from the imported centralizer, transporter,
Weyl-order and identity-component results. It does not assert a translation
of a numbered result in the literature.

Let `R` be a local domain with fraction field `K`. Let `M` be a reductive
group scheme over `Spec R` and `G` a smooth affine group scheme over the same
base. Suppose `f : M ⟶ G` is monic on underlying schemes and its pullback to
`Spec K` is an isomorphism. Supply a finite coordinate split torus
`i : splitTorus (Spec R) I ⟶ M` which is a closed subgroup and fibrewise
maximal.

The definition `SplitOpenGenericIsomorphism.closedFieldIso` additionally
assumes that `f` is an open immersion. For every algebraically closed
`R`-field `k` whose unique point maps to the closed point of `Spec R`, it
constructs an actual isomorphism

`(baseChange (algebraBaseMap R k)).obj M ≅
 (baseChange (algebraBaseMap R k)).obj G`.

The accompanying `closedFieldIso_hom` lemma identifies its forward
homomorphism with the original pullback of `f`. All types and schemes use
the same arbitrary universe `u`.

The construction proceeds through three supporting results.

1. `centralizer_eq_range` identifies the all-test torus centralizer of
   `i ≫ f` with its actual pointwise range. The split-torus monomorphism
   theorem makes the composite a closed subgroup. The generic isomorphism
   transports connected reductivity and maximality from `M` to `G`;
   `splitTorusCentralizer_eq_range_of_genericMaximal` then descends generic
   self-centralization to `R`. This lemma needs a domain and its fraction
   field, but does not require `R` to be local or `f` to be open.

2. `closedField_weylOrder_le` bounds the order of the actual point Weyl
   quotient for the torus in `G_k` by that for the torus in `M_k`. The smooth
   transporter bound compares the first order with the order over an
   algebraic closure of `K`, preserving the given `R`-algebra structure.
   Base change of the supplied generic isomorphism identifies that quotient
   with the one for `M`. The local split Weyl-order theorem for the reductive
   source identifies its orders over both fields. This supporting lemma
   only needs a local commutative ring and an `R`-field `K` on which `f` is
   an isomorphism; it does not require the domain or fraction-field
   hypotheses or openness.

3. `closedField_normalizerPoints_le_range` shows that every normalizer
   base point on the closed-field fibre is in the actual range of `f_k`.
   Source-isomorphism invariance and arbitrary base change transport the
   first centralizer equality to the coordinate torus on that fibre.
   Its range is contained in the range of `f_k`. The second result supplies
   the reverse Weyl-order bound; `normalizerPoints_le_range_of_natCard_le`
   uses finiteness of the full character image and the split centralizer
   kernel to conclude the desired normalizer containment. This result
   retains the local-domain hypotheses but needs neither algebraic closure
   of `k` nor openness of `f`.

For `closedFieldIso`, connected reductivity of `M_k` and the open immersion
`f_k` identify `M_k` with the identity component of `G_k`. The required
closedness of this field-group monomorphism comes from the published
field-image theorem. Transport `i_k` across this isomorphism. It remains a
maximal torus in the identity component, and the normalizer-containment
result above places its full normalizer in that component.
`identityComponentIsoOfNormalizerPoints` then identifies the identity
component with all of `G_k`, using the published maximal-torus conjugacy
argument over an algebraically closed field. Composing these two actual
isomorphisms gives `closedFieldIso`. Their forward-map identities give
`closedFieldIso_hom`.

The supplied split fibrewise maximal torus and generic isomorphism remain
essential inputs. This unit constructs a closed-field-fibre isomorphism;
it does not yet prove an isomorphism over `R` or the general reductive
monomorphism closed-immersion statement.
