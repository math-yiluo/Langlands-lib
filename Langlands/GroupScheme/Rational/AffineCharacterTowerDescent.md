# Descent of affine characters along a field tower

This internal unit descends characters along a tower of fields
`k -> E -> L`. Let `G` be an affine group scheme over `k`, and let `ψ` be an
actual character of the base change `G_L`. If the universal tensor value of
`ψ` has coefficients in `E`, then `ψ` comes from an actual character of
`G_E`. When `L/E` is Galois, it is enough that this tensor value is fixed by
`Gal(L/E)`. The descended character has the expected rational values and
restrictions.

The published `AffineCharacterFiniteGaloisReconstruction` handles the case
where `E` is a finite Galois intermediate field of `L/k` with `k` its base.
Here `E` is any intermediate field of an arbitrary tower, and `L/E` need not
be finite. The construction follows the same route: values defined by a
coefficient tensor satisfy the character laws, and the published
`AffineCharacterNaturalValues.character` turns natural values into an actual
character.

## Coefficient tensors and model values

`Coord G` is the published coordinate algebra, and
`AffineCharacterFiniteGalois.tensorValue G L ψ` is the value of `ψ` at the
universal point, a unit of `L ⊗[k] Coord G`.

- `tensorExtend G E L : E ⊗[k] Coord G →ₐ[k] L ⊗[k] Coord G` extends tensor
  coefficients along `E -> L`. `tensorExtend_injective` states that this map is
  injective, because both tensor factors are flat over the field `k`.
- `tensorEval_comp_tensorExtend`: for a point `y` with coefficients in an
  algebra `D` over the tower, evaluating the extended tensor at `y` over `L`
  gives the same result as evaluating it over `E`.
- `modelValue G E v D y` is the image of a unit `v` of `E ⊗[k] Coord G` under
  evaluation at `y`. Here `D` is any `E`-algebra with a compatible
  `k`-structure. `modelValue_naturality` states that this value is natural in
  maps of `E`-algebras.

Fix `ψ` and a unit `v` with `tensorExtend v = tensorValue G L ψ` (hypothesis
`hv`).

- `modelValue_eq_valueE`: over every `L`-algebra in the tower, the model value
  equals the value `valueE ψ D y` of `ψ`. This follows from the published
  `tensorValue_eval`.
- `modelValue_compare`: for an `E`-algebra `B`, the injective map
  `B -> L ⊗[E] B` sends the model value at `y` to the value of `ψ` at the image
  of `y`.
- `modelHom` packages the model values over `B` as a monoid homomorphism. The
  laws are checked after this injective scalar extension, where they are the
  laws of `ψ`.

## The descended character

`baseChanged_isAffine` records that the base change of an affine group scheme
to a field is affine. `ext_valueE` states that two characters of `T_E` are
equal when they have the same values `valueE` over every `E`-algebra with a
compatible `k`-structure. It is deduced from the published
`rationalCharacters_ext_affinePoints`.

`descendApp` transports `modelHom` to points of the actual base change `G_E`
through the published comparison `pointE`. `descendApp_naturality` states its
naturality. `descendCharacter G E L v ψ hv` is the actual character of `G_E`
that `AffineCharacterNaturalValues.character` builds from these values.
`descendCharacter_affineValues` records its values on points of `G_E`.

- `valueE_descendCharacter`: over every `E`-algebra `D`, whatever its
  compatible `k`-structure, the descended character takes the model values.
  The `k`-structure is identified with the one induced through `E`.
- `valueE_descendCharacter_of_tower`: over every `L`-algebra in the tower, the
  descended character has the values of `ψ`.
- `valueE_descendCharacter_includeRight`: over an `E`-algebra `B`, its values
  become those of `ψ` after the extension `B -> L ⊗[E] B`.
- `rationalCharacterEval_rationalExtend_of_valueE`: let `χ` be a character of
  `G_E` that has the same values as `ψ` over `L`. Then for every rational
  point `g` of `G`, `algebraMap E L (χ(g_E)) = ψ(g_L)`. The proof uses the
  published `valueE_baseChangeCoeffEquiv`, the naturality of `valueE` along
  `E -> L`, and the composition of coefficient maps `k -> E -> L`.
  `rationalCharacterEval_descendCharacter` applies this to the descended
  character.
- `characterRestrict_descendCharacter`: let `f : H -> G` be an actual
  homomorphism from an affine group scheme `H` over `k`, and `a` an actual
  character of `H`. If the restriction of `ψ` along the base change of `f` to
  `L` is the base change of `a`, then the restriction of the descended
  character along the base change of `f` to `E` is the base change of `a`.
  The proof uses `ext_valueE` and injectivity of `B -> L ⊗[E] B`, with the
  published `valueE_characterRestrict`, `valueE_baseChange` and
  `Gm.affineUnitsEquiv_naturality`.

## Galois-fixed tensors

`tensorConj G E L σ`, for `σ ∈ Aut(L/E)`, applies `σ` to the coefficients of
`L ⊗[k] Coord G`. Take the basis of `L ⊗[k] Coord G` over `L` induced by a
basis of `Coord G` over `k`. `tensorConj_repr` states that `σ` acts on the
coordinates of a tensor in this basis by applying `σ` to each coordinate.

Assume `L/E` is Galois; it need not be finite.

- `mem_range_tensorExtend_of_fixed`: a tensor fixed by every `σ ∈ Gal(L/E)`
  lies in the range of `tensorExtend`. Each of its coordinates is fixed, so it
  lies in `E` by Mathlib's `InfiniteGalois.mem_range_algebraMap_iff_fixed`.
  Summing over the support then exhibits a preimage.
- `exists_unit_of_fixed`: a fixed unit tensor is the extension of a unit of
  `E ⊗[k] Coord G`. Its inverse is also fixed, and injectivity of
  `tensorExtend` makes the two preimages inverse to each other.
- `fixedDescend G E L ψ hψ` is the descended character when the universal
  tensor value of `ψ` is fixed by `Gal(L/E)` (hypothesis `hψ`). The lemmas
  `valueE_fixedDescend`, `rationalCharacterEval_fixedDescend` and
  `characterRestrict_fixedDescend` restate the three properties above for
  this character.

## Provenance and scope

This is standard Galois descent for vector spaces, applied to the coordinate
algebra of an affine group scheme. The descent of characters is internal
infrastructure, built from the published finite Galois reconstruction route.
The unit does not show that a particular character, such as a root of a
torus, has a Galois-fixed universal tensor value; applications must prove
that hypothesis. All results hold in every universe `u` and for arbitrary
fields. The only assumptions are the stated affineness, the scalar tower and,
for the last section, that `L/E` is Galois.
