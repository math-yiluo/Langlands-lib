# Uniqueness target for universal rigidified line bundles

`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.UniversalBundleUniquenessStatement`
is the proposition that two universal rigidified line bundles have a unique
compatible isomorphism of their parameter schemes. This module states it and
contains no proof. It is proved, exactly as stated, by
`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.universalBundleUniqueness`
in module `Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalUniquenessProof`.

More precisely, suppose `f : X → S` has a section `ε`. Let `P` and `Q` be
`S`-schemes, with actual rigidified line bundles `L` on `P ×_S X` and `M`
on `Q ×_S X`. If `IsUniversal L` and `IsUniversal M`, there exists exactly
one isomorphism `e : P ≅ Q` in `Over S` such that the actual pullback
`e* M` is isomorphic to `L` as a rigidified line bundle. Compatibility is
the proposition `Nonempty (e* M ≅ L)`. The uniqueness quantifier concerns
`e`; it does not assert uniqueness of the bundle isomorphism or claim
that the parameter schemes have no other automorphisms.

The statement takes
`RigidifiedModule.PullbackCoherenceStatement` as an explicit hypothesis,
at the same universe as the schemes. This is the precise canonical
identity/composition compatibility proposition used to construct the
class presheaf and its representability bridge. No extra coherence
axiom is introduced. The proof `universalBundleUniqueness` also keeps this
hypothesis. It uses the two classifying maps together with the pullback
identity and composition laws `classifyingMap_id` and `classifyingMap_comp`,
which need the hypothesis. Equality of classes is equivalent to existence of
the required rigidified bundle isomorphism (`classifyingMap_eq_iff`). The
hypothesis itself is proved separately, as
`Langlands.SchemeModule.RigidifiedModule.pullbackCoherence` in module
`Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs`. So
`universalBundleUniqueness pullbackCoherence` proves the quantified
uniqueness assertion with no coherence hypothesis left.

This is a derived Yoneda uniqueness target for the universal property in
Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI §1, (6.2),
printed p.88 (PDF p.92), paragraph defining the Poincaré bundle and its
universal property. The retained source is registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The source states the unique classifying-map property and discusses
uniqueness of a representing scheme; the compatible-isomorphism
formulation here is its categorical consequence. As in
`RigidifiedUniversalBundle`, the fibre product is written in the
canonically symmetric order `T ×_S X`.

The target quantifies over arbitrary schemes and sections. Additional
hypotheses in the source for comparison with the fppf Picard sheaf and
the absence of bundle automorphisms are unnecessary for uniqueness of
the parameter-scheme isomorphism. There is no claim here that universal
bundles exist or that the class presheaf has an abelian group law.
