# Normalizer equivariance of central-isogeny root-function pullback

This is an internal derived compatibility construction for the supplied square
used in `CentralIsogenyFunctions` and `CentralIsogenyNormalizerAction`.
All constructions work over a field in arbitrary universe `u`.

Let `i : S.toGrp ⟶ C` and `j : T.toGrp ⟶ G` be monomorphic torus
homomorphisms, with splitness proofs `hS`, `hT`, an isogeny `t : S ⟶ T`,
an ambient homomorphism `q : C ⟶ G`, and the square
`i ≫ q = groupHom t ≫ j`. Write `Nq` for the actual normalizer map
`splitTorusIsogenyNormalizerMap q hS hT t h ht`.

`weylAction_splitTorusIsogenyNormalizerMap` proves
`t ≫ weylAction j (Nq n) a = weylAction i n (t ≫ a)`.
The proof composes the existing normalizing-automorphism square with the two
inverse automorphisms, then postcomposes with the character. It uses the original
inverse-precomposition character actions.

`realizesReflection_splitTorusIsogenyNormalizerMap_iff` proves
`RealizesReflection j a (Nq n) ↔ RealizesReflection i (t ≫ a) n`.
Flatness and scheme surjectivity of the torus isogeny give injectivity of actual
character restriction. The existing isogeny theorem gives bijectivity on real
cocharacters. Together with the character, cocharacter and evaluation identities,
these compare both the negated-character condition and pointwise fixedness of the
character kernel. These two results do not require an ambient central isogeny or
affine or finite-type hypotheses.

`RootFunctionFamily.IsNormalized.smul` states that the actual normalizer action
preserves the two normalization conventions. Here only the ambient group of the
family must be affine, and its torus embedding must be monomorphic. The Weyl
action preserves and reflects actual roots; actual conjugation preserves and
reflects the corresponding root-subgroup membership on every test scheme. The
proof specializes this last assertion to rational points.

For the remaining constructions assume additionally that `C` and `G` are affine
and locally of finite type and `q` is a central isogeny. Let `P` denote the actual
normalized pullback from `CentralIsogenyFunctions`.
`RootFunctionFamily.centralIsogenyNormalizedPullback` packages `P` as a map
between the types of normalized families. Its injectivity is proved using the
existing pullback injectivity theorem and subtype extensionality.

`RootFunctionFamily.centralIsogenyPullback_smul` proves
`P (Nq n • φ) = n • P φ` for every full target family `φ`.
On an actual source root subgroup the character comparison identifies the
corresponding target roots, and naturality of the ambient point homomorphism
identifies conjugation. Off a source root or source root subgroup, both sides are
infinity by normalization and the actual conjugation membership equivalence.
No normalization premise on `φ` is needed for this identity.

For a normalized target family,
`equipollent_smul_centralIsogenyPullback_iff` consequently proves
`Equipollent (P φ) (n • P φ) ↔ Equipollent φ (Nq n • φ)`.
It combines the preceding action identity with preservation and reflection of
equipollence by `P`; normalizer preservation of normalization supplies the second
target normalization proof.

The provenance is the derivation just described from actual torus and root
actions, rather than a separate assertion from the literature. The supplied tori,
embeddings, square and isogeny remain inputs. This unit does not construct a full
root-datum valuation, an apartment equivalence, source apartment axioms or a proof
of the final normalizer-image theorem.
