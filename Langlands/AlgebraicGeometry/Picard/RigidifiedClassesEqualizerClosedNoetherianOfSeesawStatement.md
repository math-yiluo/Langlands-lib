# The noetherian affine agreement locus from the noetherian seesaw (statement)

Author: Worker 766.

This module defines one proposition and proves nothing:

```lean
def Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedNoetherianOfSeesawStatement : Prop :=
  NoetherianLineBundleSeesawStatement.{u} →
    RigidifiedClassesZariskiSeparatedStatement.{u} →
      SmoothGeometricIntegrality.{u} →
        RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u}
```

It is the implication "the noetherian seesaw, Zariski separatedness and smooth geometric
integrality together give the noetherian affine agreement locus". It links four published
propositions:

- `Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawStatement` (module
  `Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawStatement`). Let
  `c : X ⟶ Spec R` be proper, flat and geometrically integral, and assume the canonical map on
  global functions is bijective after every affine base change `Spec B ⟶ Spec R`. Let `T` be a
  locally noetherian scheme over `Spec R`, and `M`, `M'` two locally free rank-one sheaves on
  `X ×_{Spec R} T`. Then there is a closed immersion `ι : Z ⟶ T` such that a morphism
  `ψ : T' ⟶ T` factors through `ι` exactly when the pullbacks of `M` and `M'` to
  `(X ×_{Spec R} T) ×_T T'` are isomorphic over an open neighbourhood in `T'` of each point of
  `T'`.
- `Langlands.AbelianScheme.RigidifiedClassesZariskiSeparatedStatement` (module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedStatement`). Two actual
  rigidified classes on `T ×_S A` are equal if they agree after pullback to every member of a
  Zariski open cover of `T`. This holds for every scheme `S`, abelian scheme `A` over `S`,
  object `T : Over S` and open cover indexed in universe `u`.
- `Langlands.AbelianScheme.SmoothGeometricIntegrality` (module
  `Langlands.AbelianScheme.SmoothGeometricIntegralityStatement`): for every field `K` in universe
  `u`, every smooth and geometrically connected `p : X ⟶ Spec K` is geometrically integral.
- `Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedNoetherianAffineStatement` (module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianStatement`). For
  a noetherian ring `R`, an abelian scheme `A` over `Spec R`, and two rigidified classes `q`, `r`
  over `Over.mk (𝟙 (Spec R))`, there is a closed immersion `ι : Z ⟶ Spec R` with the following
  property. A morphism `h : T' ⟶ Over.mk (𝟙 (Spec R))` has `h.left` factoring through `ι`
  exactly when the pullbacks of `q` and `r` along `h` are equal.

The universe parameter `u` is shared by all four propositions. The definition asserts none of
them; it states only the implication.

## Provenance

Internal to this project. The four propositions have their own provenance, described in their
Markdown files. The seesaw and the noetherian affine statement are both derived from the Stacks
Project, *More on Morphisms*, Section 37.33: Lemma 37.33.1 (tag 0BDP) and Lemma 37.33.4 (tag 0BF0).
The registered source is `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`. The implication
records how the abelian-scheme statement reduces to the general seesaw for the pair of carrier
sheaves (Stacks applies the lemmas to `E = L ⊗ L'⁻¹`). The seesaw is applied to the structure
morphism of `A`. Its hypotheses are checked for an abelian scheme:

- properness and flatness come from the abelian scheme;
- geometric integrality comes from smoothness and geometric connectedness of the fibres, via
  `SmoothGeometricIntegrality`;
- bijectivity of global functions after affine base change is the published theorem
  `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`.

The seesaw only produces isomorphism of the underlying sheaves locally on the test scheme. That
is turned into equality of the actual rigidified classes in two steps. First, the
rigidification is recovered from the underlying isomorphism, which is
`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.nonempty_iso_of_forget_iso`. Second, the local equalities are glued by
`RigidifiedClassesZariskiSeparatedStatement`.

This decomposition was chosen for task `00ab6acd-8b6c-4595-8df8-3fbdac0bdd4d`, which proves the
noetherian affine statement. Worker 1048 published the seesaw statement in that task; its proof
is being ported there from the Anthropic FLT Lean source.
