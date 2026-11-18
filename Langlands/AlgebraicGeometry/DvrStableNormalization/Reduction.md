# Stable normal models from the affine reduced fibre theorem

Worker 6.

## The model

`Langlands.AlgebraicGeometry.DvrStableNormalization.model X hfin hgr : DvrStableNormalization.Model X`
is the stable normal model of `X` over a DVR `R`. Here `X : Over (Spec R)` is flat and locally of
finite type with smooth generic fibre `X ×_{Spec R} Spec (Frac R)`. Its fields are:

- `source := source X`, Mathlib's relative normalization of `X` in its generic fibre (see
  `Model.md`), and `map := map X`, the normalization map to `X`;
- `finite := hfin` and `geometricallyReduced := hgr`, the two inputs: `map X` is finite and
  `source X` is geometrically reduced over `Spec R`;
- `surjective` and `flat` from `FlatSurjective.lean`, `genericIso` from `Model.lean`;
- `normal_powers` from `Powers.lean`: every fibre power is flat, locally of finite type and
  geometrically reduced, with smooth generic fibre, hence has normal stalks;
- `normal_lift` from `Model.lean`: for a flat `T` with normal stalks, composition with `map X` is
  a bijection `(T ⟶ source X) → (T ⟶ X)`.

`source X` plays the role of the normalization `~X'` in Conrad's Theorem A.2 and Corollary A.4.
Taking the normalization of `X` in its generic fibre, rather than the absolute normalization, is
an internal formalization choice; the Lean development does not compare the two. `model` takes
finiteness of `map X` and geometric reducedness of `source X` as explicit hypotheses. Theorem A.2
provides them only after a suitable extension of the DVR; the reduction below supplies them.

## The reduction

`Langlands.AlgebraicGeometry.DvrStableNormalization.dvrStableNormalization_of_affineReducedFibre`
proves

`DvrAffineReducedFibreStatement.{u} → DvrStableNormalizationStatement.{u}`.

So the Library target `DvrStableNormalizationStatement` holds in every universe, with no
additional hypotheses, once the affine reduced fibre theorem `DvrAffineReducedFibreStatement`
is proved.

### Proof

Let `X` be flat, locally of finite type, quasi-compact and separated over a DVR `R`, with smooth
generic fibre.

1. Apply `DvrAffineReducedFibreStatement` once to `A = Γ(coverOver X, ⊤)`, the global sections of a
   finite affine cover of `X`. The three hypotheses come from `AffineHypotheses`. This gives a DVR
   `R' : Type u` with `Module.FaithfullyFlat R R'`, so `b = Spec R' → Spec R` is flat and surjective
   (`flat_and_surjective_SpecMap_iff`).
2. The base change `X'` of `X` along `b` is flat and locally of finite type. Its generic fibre is
   smooth by Library `Langlands.GroupScheme.DvrCoverAssembly.smooth_generic`.
3. `finite_geometricallyReduced_of_cover` shows that the normalization of `X'` in its generic fibre
   is finite over `X'` and geometrically reduced over `Spec R'`.
4. `model` applied to these two facts is the required `DvrStableNormalization.Model` of `X'`.

## Provenance

This derivation follows the route described in the paired Markdown of
`DvrStableNormalizationStatement`. It uses Conrad's appendix to Prasad–Yu, *On quasi-reductive
group schemes*, pp.28–29: Theorem A.2 and Remark A.1 (here the hypothesis), Remark A.3 (normality
of fibre powers), and Corollary A.4 (the universal-property lifting argument). Registered source
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
