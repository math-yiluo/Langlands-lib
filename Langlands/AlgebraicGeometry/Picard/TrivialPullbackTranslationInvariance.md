# Translation invariance from invariance of the kernel character

This module turns the shear invariance of
`Langlands.AbelianScheme.KernelCharacterShearInvariance` into translation
invariance of an ordinary line bundle on `B`. It works over an arbitrary
base `S`, for an arbitrary homomorphism `f : A ⟶ B` of abelian schemes. Its
main theorem is conditional. It assumes two explicit inputs: every section of
`B` over `S` lifts through `f`, and the class character over the base itself
is injective. This module proves neither input.

Composition `p ≫ q` means "first `p`, then `q`". `T₀` denotes the object
`Over.mk (𝟙 S)` of `Over S`.

## Line bundle pullback along isomorphisms

- `LineBundle.pullbackInvPullbackIso`: for an isomorphism of schemes
  `p : X ⟶ Y` and a line bundle `M` on `Y`, it gives an isomorphism
  `(inv p)^* p^* M ≅ M`. The construction is the published `pullbackComp`
  for `inv p ≫ p`, followed by `eqToIso` along `inv p ≫ p = 𝟙 Y` and by
  `pullbackId`.

- `LineBundle.nonempty_iso_of_pullback_iso`: for such a `p`, an isomorphism
  `p^* M ≅ p^* N` gives `Nonempty (M ≅ N)`. The proof pulls the isomorphism
  back along `inv p` and conjugates it with the previous isomorphism.

## The relative space over the base itself

- `baseRelativeSnd B`: the second projection
  `pullback.snd (𝟙 S) B.X.hom` from the relative space
  `(relativeSpace B.X.hom).obj T₀ = S ×_S B` to `B.X.left`. The accompanying
  instance shows that it is an isomorphism, because it is a base change of
  the isomorphism `𝟙 S`.

- `shear_baseRelativeSnd`: for a section `x : T₀ ⟶ B.X`, the shear by `x`
  over `T₀` corresponds to translation by `x` under this projection:
  `shear B (𝟙 T₀) x ≫ baseRelativeSnd B =
  baseRelativeSnd B ≫ (translation B.toGrp x).left`. The proof rewrites the
  left side with `shear_snd` and the right side with the published
  `points_translation`. The two remaining maps to `T₀` are equal because
  `T₀` is terminal (`Over.mkIdTerminal.hom_ext`).

- `hasTrivialHomPullback_baseRelativeSnd`: let `L` be a line bundle on `B`
  with a nonempty module isomorphism
  `(Scheme.Modules.pullback (hom f)).obj L.obj ≅ O_A`. Then the line bundle
  pullback of `L` along `baseRelativeSnd B` satisfies
  `HasTrivialHomPullback f T₀`. The required trivialization is the published
  `squarePullbackIso` for the square `homFamilySpaceMap_snd`, which says
  `f_{T₀} ≫ snd_B = snd_A ≫ hom f`. It is followed by the pullback of the
  given isomorphism along `baseRelativeSnd A` and by `pullbackUnitIso`.

## Translation invariance

- `nonempty_translation_pullback_iso`: assume that
  `trivialHomPullbackClassCharacter f (T := T₀) (universalGlobalFunctions A)`
  is injective. Let `L` on `B` have a module isomorphism
  `(hom f)^* L ≅ O_A`, and let `a : T₀ ⟶ A.X` be a section. Then there is a
  nonempty isomorphism
  `(LineBundle.pullback (translation B.toGrp (a ≫ (groupHom f).hom.hom)).left).obj L ≅ L`.
  The proof applies `nonempty_shear_pullback_iso` with `T := T₀` and the
  point `a` to the pullback of `L` along `baseRelativeSnd B`, using the
  previous lemma. The pullback of the translate along `baseRelativeSnd B` is
  then identified with the shear pullback. This uses `pullbackComp` twice and
  `shear_baseRelativeSnd` through `eqToIso`. Finally
  `LineBundle.nonempty_iso_of_pullback_iso` removes the isomorphism
  `baseRelativeSnd B`.

- `isTranslationInvariant_of_trivialHomPullback`: suppose that every section
  `x : T₀ ⟶ B.X` has the form `a ≫ (groupHom f).hom.hom` for some section
  `a : T₀ ⟶ A.X`. Suppose also that the class character over `T₀` is
  injective as above. Then every line bundle `L` on `B` with
  `(hom f)^* L ≅ O_A` satisfies `GroupScheme.IsTranslationInvariant B.toGrp L`.
  The proof lifts the given section and applies the previous theorem.

## Scope and provenance

No field, isogeny, reducedness or properness assumption occurs beyond what
the abelian-scheme structures carry. The two inputs of the final theorem,
section lifting and injectivity of the class character over `T₀`, remain
explicit hypotheses. For the target `FieldTrivialPullbackPicardZeroStatement`
they are to be supplied separately, over an algebraically closed field and
for an isogeny `f`.

The provenance is internal. The module records the classical observation
that a line bundle `L` with `f^*L` trivial is invariant under translation by
every point in the image of `f`. Here this comes from the invariance of the
attached kernel character, proved in `KernelCharacterShearInvariance`.
