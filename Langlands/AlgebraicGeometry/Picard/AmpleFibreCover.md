# Finite covers of a base by fibre-ample loci

This helper module, in namespace `Langlands.AlgebraicGeometry.Picard`, introduces an internal
bookkeeping predicate for the proof of `RelativeDualSchemeQuasiCompactStatement` and proves two
transport lemmas for it.

## Definition

`HasAmpleFibreCover f V`, for `f : X ⟶ S` and a set `V ⊆ S`, is the proposition that there exist
the following data:

- a finite index type `ι : Type u`;
- for each `i`, schemes `T i` and `W i`, maps `g i : T i ⟶ S`, `a i : W i ⟶ X` and
  `q i : W i ⟶ T i`, and a line bundle `L i` on `W i`;

such that the following hold:

- each square `IsPullback (a i) (q i) f (g i)` is Cartesian, so `W i` is the base change of `X`
  to `T i`;
- each `T i` is affine;
- each `g i` has range contained in `V`;
- every `s ∈ V` equals `g i t` for some `i` and some `t ∈ ampleFibreLocus (q i) (L i)`.

Informally, `V` is covered by finitely many images of fibre-ample loci of line bundles on base
changes of `X` to affine schemes. The definition is internal; it has no literature source.

## Results

- `HasAmpleFibreCover.of_isPullback hp hc`. Let `hp : IsPullback α f f' h` be a Cartesian square
  with `f : X ⟶ S`, `f' : X' ⟶ S'` and `h : S ⟶ S'`. Then `HasAmpleFibreCover f V` implies
  `HasAmpleFibreCover f' (h '' V)`. The same data are used, with the bottom maps replaced by
  `g i ≫ h` and the top maps by `a i ≫ α`. The squares paste horizontally
  (`IsPullback.paste_horiz`), and the cover condition is carried along `h`.
- `HasAmpleFibreCover.baseChange hp hc`. Let `hp : IsPullback α f₁ f₀ φ` be a Cartesian square
  with `S₀` and `S₁` affine. Then a cover `HasAmpleFibreCover f₀ Set.univ` gives
  `HasAmpleFibreCover f₁ Set.univ`. The construction is:
  1. Put `T' i = T i ×_{S₀} S₁`, which is affine because a fibre product of affine schemes is
     affine. Put `W' i = W i ×_{T i} T' i`, and take `q' i` to be the second projection.
  2. Pull the line bundle back to `W' i`.
  3. Obtain the map `a' i : W' i ⟶ X₁` from the universal property of `hp`. Its square is
     Cartesian by `IsPullback.of_right`, after pasting.
  4. For the cover condition, take `s ∈ S₁`. The cover over `S₀` provides `t ∈ T i` over `φ s`.
     `Scheme.Pullback.exists_preimage_pullback` gives `t' ∈ T' i` over both `t` and `s`.
  5. `mem_ampleFibreLocus_iff_of_isPullback` shows that `t'` lies in the fibre-ample locus of the
     pulled-back bundle.

## Provenance

Internal helper definition and lemmas, derived for this proof. The fibre-ample locus and its
invariance under base change are the published `ampleFibreLocus` and
`mem_ampleFibreLocus_iff_of_isPullback` in `FibreAmplenessBaseChange`.
