# Actual dual maps as commutative-group-scheme homomorphisms

This module makes the existing contravariant dual morphism into a
homomorphism between the commutative group schemes constructed in
`DualGroupScheme`. It proves identity and composition laws for these
bundled homomorphisms and identifies their action on points with actual
pullback of rigidified geometric Picard-zero classes.

## Source and provenance

The construction is derived from the published `DualSchemeMap`,
`DualSchemeMapTensor`, `DualSchemeMapMonoid`, and `DualGroupScheme`
modules. The source convention for rigidification, tensor multiplication,
parameter pullback and universal Poincaré classification is
Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft,
Chapter VI, paragraph (6.2), printed p.88 (PDF p.92).

Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`.
Content SHA-256:
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The cited paragraph defines the rigidified functor and its tensor
multiplication, and describes the unique classifying map of a rigidified
family under a universal Poincaré family. The present module restricts
the existing constructions to the published geometric Picard-zero
subtype. Its additional group-scheme packaging follows from the already
proved origin and tensor preservation equations. It does not invoke the
source's identification with the fppf Picard sheaf; the hypotheses
required for that identification are not removed or generalized here.

## Inputs and conventions

The base `S : Scheme.{u}` is arbitrary. The objects `A`, `B`, and, for
composition, `C` are the existing abelian schemes over `S`. A proof
`hA : HasDualScheme A` supplies a universal rigidified geometric
Picard-zero family, determining `dualScheme A hA`; likewise for the
other endpoints.

At each endpoint the construction retains an explicit ordinary line
bundle `MA` on the parameter-first relative space `D_A ×_S A` and an
actual module-sheaf isomorphism
`P_A ⊗ MA ≅ O`, where `P_A` is the chosen Poincaré family. These are the
inputs used by `dualCommGroupSchemeFromEvaluation`. They supply no
assumed homomorphism law for the dual map.

The following fixed-map propositions remain explicit:

- `pullbackTensorComparisonIsIsoStatement`;
- `PullbackTensorCompositionStatement`;
- `PullbackTensorUnitCoherenceStatement`;
- `ExplicitPullbackTensorAssociativityStatement`;
- `TensorMonoidalLeftUnitorComparisonStatement`;
- `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement`.

They assert preservation and coherence for the previously defined
maps. Homomorphism pullback preservation of the geometric Picard-zero
condition uses the published proof `homPicardZeroPullback`.
Identity and composition use the published rigidified pullback
coherence proof `Langlands.SchemeModule.RigidifiedModule.pullbackCoherence`.

## Construction and implemented proofs

For `f : A ⟶ B`, `dualCommGroupSchemeMapFromEvaluation` has type
`G_B ⟶ G_A`, where each `G` is the corresponding
`dualCommGroupSchemeFromEvaluation`. The existing category of
commutative group schemes uses additive notation for its homomorphisms.
The definition wraps a Mathlib `Grp.homMk''` in `Additive.ofMul`;
its underlying morphism in `Over S` is exactly
`dualSchemeMap homPicardZeroPullback f hA hB`.

The unit law reduces, after the structural map from the chosen monoidal
unit, to `dualSchemeMap_origin`. For multiplication, the reconstructed
group law is tensor classification after the canonical comparison from
the cartesian monoidal product to the chosen categorical product.
The proof applies `dualSchemeMap_tensor` and the projection identities
for both products. Thus the bundled homomorphism uses the actual tensor
group laws at both endpoints.

`dualCommGroupSchemeMapFromEvaluation_hom` records the equality with the
existing underlying dual morphism by reflexivity. The identity lemma
proves `dual(id_A) = id_{G_A}`. The composition lemma proves
`dual(f ≫ g) = dual(g) ≫ dual(f)`, allowing separate inverse bundles and
evaluations at all three endpoints. Both proofs use injectivity of the
additive wrapper and extensionality of group-object homomorphisms,
then apply the published identity and composition equations for
`dualSchemeMap`.

For every test scheme `T : Over S` and point `p : T ⟶ G_B.X`,
`dualCommGroupSchemeMapFromEvaluation_classification` proves

`class_A(dual(f)(p)) = f^*(class_B(p))`.

Here `class_A` and `class_B` are the actual multiplicative Poincaré
equivalences `dualCommGroupSchemePointMulEquiv`. The point map is
`Langlands.GroupScheme.pointsMap` of the bundled homomorphism, and the
right-hand map is `homPicardZeroPullbackMonoidHom`. Their definitions
reduce the assertion to the already proved
`dualPointClass_dualSchemeMap`. No reducedness, affineness or field
restriction is imposed on `T`.

## Scope

This is a conditional construction for chosen duals with the displayed
inverse bundles, evaluations and coherence hypotheses. It does not
prove existence of those inputs, or that the resulting group schemes
are smooth, proper or geometrically connected. It proves that the dual
map for each fixed `f` is a group-scheme homomorphism. Additivity of the
assignment as `f` varies, its rational extension, and polarizations
remain separate obligations.
