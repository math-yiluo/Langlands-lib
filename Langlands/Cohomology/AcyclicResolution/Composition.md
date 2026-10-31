# Composite-functor comparison through a right resolution

Let `C` and `D` be abelian categories. Their object and morphism universes
are independently quantified. For an additive functor `F : C ⥤ D`, an
object `A : C`, a natural-indexed cochain complex `K`, and an arbitrary
augmentation `ε : A[0] → K`, the selected definition
`mapResolutionAugmentation F ε` is the actual map

```text
F(A)[0] → F(K).
```

It is the inverse component at `A` of Mathlib's
`singleMapHomologicalComplex`, followed by the image of `ε` under
`F.mapHomologicalComplex`. This definition requires no injective
resolutions or quasi-isomorphism assumption.

The lemma `mapResolutionAugmentation_f_zero` identifies its component
in degree zero with `F.map (ε.f 0)`, using the canonical degree-zero
identifications of single complexes. For an injective resolution `I`
of `A`, the lemma `mapResolutionAugmentation_injectiveResolution`
proves equality with the published `mapAugmentation F I`. Extensionality
for maps from a degree-zero single complex reduces this equality to the
degree-zero component.

For any second augmentation `η : B[0] → L` and maps `a : A → B`,
`t : K → L` with `ε ≫ t = single₀.map a ≫ η`, the lemma
`mapResolutionAugmentation_naturality` proves

```text
mapResolutionAugmentation F ε ≫ F(t)
  = single₀.map (F.map a) ≫ mapResolutionAugmentation F η.
```

This follows from functoriality and naturality of the inverse
single-complex comparison.

Now let `E` be another abelian category, again with independent object
and morphism universes. Assume that `C` and `D` have injective
resolutions. Let `G : D ⥤ E` and `H : C ⥤ E` be additive, and fix
`e : F ⋙ G ≅ H`. Assume that `F` preserves finite limits. For
`A : C` and `ε : A[0] → K`, the theorem
`resolutionComparison_compComparison` assumes all of the following:

- `ε` is a quasi-isomorphism;
- `mapResolutionAugmentation F ε` is a quasi-isomorphism;
- `hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)`.

For every `n : ℕ`, it proves the exact equality

```text
resolutionComparison H ε n ≫ compComparison G e A hA n
  =
Hⁿ((mapHomologicalComplexCompIso e).inv.app K) ≫
  resolutionComparison G (mapResolutionAugmentation F ε) n.
```

Both sides go from `Hⁿ(H(K))` to `RⁿG(F(A))`.
Here `compComparison` is the published comparison constructed using
Mathlib's chosen injective resolution of `A`. The right-hand side
uses the inverse termwise composite-functor isomorphism and the
published right-resolution comparison for the mapped augmentation.
There is no exactness assumption on `G` or `H`, and no termwise
acyclicity assumption on `K`.

The proof lifts `K` to the chosen injective resolution `I` of `A`
using `lift ε (𝟙 A) I.ι`. The identity `comp_lift_id` makes this a
map of augmentations. Applying `F` and the mapped-augmentation
identity gives a map to `mapAugmentation F I`. The hypothesis `hA`
ensures that this latter augmentation is a quasi-isomorphism by the
published `quasiIso_mapAugmentation`. The proof then rewrites
`resolutionComparison H ε n` using this lift, expands the published
`compComparison`, and cancels the chosen resolution's canonical
homology isomorphism and its inverse. Naturality of the inverse
termwise `e` comparison and `resolutionComparison_naturality` for `G`
give the asserted equality. The `reassoc` attributes provide the
corresponding postcomposition identities.

This is internal categorical infrastructure derived from the published
`AcyclicResolution.Comparison` and `Modules.PushforwardComparison`
constructions and Mathlib's additive single-complex comparison. It
uses no new external mathematical assertion. In particular, the mapped
augmentation's quasi-isomorphism remains an explicit hypothesis; the
theorem does not establish that applying an arbitrary left exact functor
to a resolution preserves its exactness. The equality specifies
comparison maps and does not assert their invertibility or establish
a geometric base-change or relative cube theorem.
