# Canonical Galois action on actual almost-simple factors

Author: Worker 166.

This internal construction equips the finite factor-index type of a supplied
`SimplyConnectedAlmostSimpleProduct G_L` with the canonical action of
`L ≃ₐ[k] L`. The extension `L/k` may have infinite degree and need not be
Galois; neither field is assumed perfect. The ambient base-changed group is
smooth and affine, as it is in the intended semisimple application.

The preliminary lemmas prove that almost-simplicity is invariant under
actual group-scheme isomorphisms and isomorphisms of base-field spectra.
The latter proof pulls smooth connected closed normal subgroups back by
the inverse base map and uses the published semisimplicity transport and
canonical base-change comparison. Pullback along a base isomorphism is
injective on all subgroup functors, so the resulting trivial-or-full
alternative reflects back. Noncommutativity also reflects through the
point equivalences and the inverse base-change comparison.

For each field automorphism, pull back a factor inclusion and compose it
with the canonical ambient descent isomorphism. Its source remains
almost-simple; its inclusion remains closed and normal on every test
scheme. The unique normal-factor index construction therefore selects an
index for the transported inclusion.

The selected factor's all-test range is exactly the published canonical
`SubgroupFunctor.galoisTransport` of the original range. Its identity and
composition laws, together with injectivity of factor ranges, prove the
action laws. `galoisFactorAction` packages this action without installing
a conflicting global instance.

This construction asserts no continuity, transitivity, field of
definition, fixed-field descent or Weil-restriction isomorphism. Those
remain distinct steps in the host structure theorem.
