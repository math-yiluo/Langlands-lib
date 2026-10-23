# Tensor stability of local equivalences of scheme-module presheaves

The theorem `Langlands.Scheme.Modules.tensorLocalEquivalencesIsMonoidal`
proves the existing proposition
`Langlands.Scheme.Modules.tensorLocalEquivalencesIsMonoidalStatement X`
for every `X : AlgebraicGeometry.Scheme.{u}`, with no additional hypotheses.

Let `J = Opens.grothendieckTopology X`, and let `W` be the inverse image of
`J.W` under the functor forgetting module presheaves to abelian-group
presheaves. The conclusion is `W.IsMonoidal` for the sectionwise tensor
product: identities and composites belong to `W`, and tensoring a morphism
in `W` on either side by any module presheaf preserves membership in `W`.
The theorem does not impose flatness, quasicoherence, local freeness, or
affineness.

## Implemented proof

First, multiplicativity of `J.W` gives multiplicativity of `W`. The proof
checks the identity and composition conditions using the corresponding
functoriality equations of `PresheafOfModules.toPresheaf`.
`MorphismProperty.IsMonoidal.mk'` then reduces the remaining goal to closure
of `W` under tensoring two morphisms.

For morphisms `f` and `g` in `W`, the conservative family of points of the
open-set site detects whether the underlying abelian-group morphism of
`f ⊗ₘ g` is a local equivalence. This is the equivalence supplied by
`Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology X`
and its `W_iff` lemma.

Fix a point `Φ` in this family. Write `π` for the projection from the
category of elements of `Φ.obj.fiber` to the open-set category. This is a
small cofiltered category in the required universe. Define `P` as restriction
of module presheaves along `π`, implemented by
`PresheafOfModules.pushforward₀OfCommRingCat π X.presheaf`, and let `L` forget
the restricted modules to abelian-group presheaves and then take their
colimit. The point-fiber functor is definitionally this restriction followed
by the colimit. The hypotheses on `f` and `g`, through `W_iff`, therefore
give `IsIso (L.map (P.map f))` and `IsIso (L.map (P.map g))`.

Apply the published algebraic theorem
`Langlands.Algebra.Modules.tensorColimitIsIso` to the restricted ring
presheaf `π.op ⋙ X.presheaf`. It gives
`IsIso (L.map (P.map f ⊗ₘ P.map g))`. The restriction functor `P` is strong
monoidal, so `Functor.Monoidal.map_tensor` expresses
`P.map (f ⊗ₘ g)` as this tensor morphism composed with the invertible tensor
comparison maps. Functoriality of `L` and closure of isomorphisms under
composition give invertibility of `L.map (P.map (f ⊗ₘ g))`.
Since this holds at every point of the conservative family, `f ⊗ₘ g`
belongs to `W`. Together with multiplicativity, `IsMonoidal.mk'` supplies
both required tensor-whiskering conditions.

## Provenance

This is an internal proof of the published scheme-module statement. Its
mathematical provenance is recorded in the paired Markdown for
`Langlands.AlgebraicGeometry.Modules.TensorLocalizationStatement`. The
implemented argument uses conservative points and the independently proved
varying-ring colimit theorem from
`Langlands.Algebra.Modules.TensorColimit`. The relevant Mathlib interfaces are
`Mathlib.Topology.Sheaves.Points` and
`Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal`.
The proof uses the sectionwise tensor of presheaves and constructs no
monoidal structure on sheaves.
