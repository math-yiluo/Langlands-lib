# Effective descent of line bundles along affine faithfully flat morphisms

Module `Langlands.AlgebraicGeometry.Modules.LineBundleDescentEffectiveProof`.

## Main result

`Langlands.Scheme.Modules.lineBundleDescentEffective :
LineBundleDescentEffectiveStatement.{u}` proves the Library proposition
`Langlands.Scheme.Modules.LineBundleDescentEffectiveStatement` (module
`Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStatements`). Let
`p : X ⟶ Y` be affine, flat and surjective, let `F` be a line bundle on `X`,
and let `θ` be descent isomorphisms on all pairs with equal composites that
satisfy naturality and the cocycle law. Then there is a line bundle `M` on `Y`
with `p^*M ≅ F`.

The proof packages `θ` as `D : Datum p F` (`LineBundleFlatDescentStr`). It
applies the affine core `exists_str` (`LineBundleFlatDescentCore`) to every
member of `Y.affineCover`, glues the resulting line bundles with the published
`LineBundleGluingData`, and glues an isomorphism `p^*M ≅ F` on the cover
`Y.affineCover.pullback₁ p` of `X` with the published
`openCoverIsoGluing_of_homGluing OpenCoverHomGluing.openCoverHomGluing`.

## Auxiliary lemmas (namespace `Langlands.Scheme.Modules.LineBundleFlatDescent`)

- `square_compat_of_tr_eq`: the overlap condition of the published
  isomorphism gluing (square comparisons) follows from equality of the
  transports `tr` of the two local isomorphisms to the common composite.
- `square_compIso_coherence`: a square comparison followed by composition
  comparisons equals the composition comparisons along the other side of the
  square.
- `Str.hom_ext'`: `Str.hom_ext` stated for morphisms that are isomorphisms.
- `cocycle_of_str`: let `S i : Str D (𝒰.f i) (N i)` be descended structures on
  line bundles over the members of an open cover `𝒰` of `Y`. Suppose the
  transitions `φ i j` on `pullback (𝒰.f i) (𝒰.f j)` are compatible with the
  restrictions of `S i` and `S j`. Then the transitions satisfy the cocycle
  condition `OpenCoverModuleGluing.CocycleCondition` of the published module
  gluing. On a triple overlap, each of the six factors (pullbacks of
  transitions and square comparisons) is compatible with suitable twofold
  restrictions (`Hom.restrict`, `Hom.square`). Both sides of the cocycle
  identity are therefore compatible with the same two structures, and
  `Str.hom_ext'` identifies them.
- `hom_overlap_of_compat`: if `ψ i : (𝒰.f i)^*M ≅ N i` satisfy the overlap
  compatibility of the published `LineBundleGluingData.moduleIso_compatible`,
  the square comparison of `M` is compatible with the restrictions of the
  transferred structures `(S i).transfer (ψ i)` and `(S j).transfer (ψ j)`.
- `overlap_comparison`: given such compatibilities, for `h₁ : Z ⟶ 𝒰.X i` and
  `h₂ : Z ⟶ 𝒰.X j` with the same composite `z` to `Y` and any `c : Z ⟶ X` over
  `z`, the comparisons `z^*M ≅ c^*F` obtained from the two transferred
  structures agree. The proof evaluates the overlap compatibility at the lift
  `Z ⟶ pullback (𝒰.f i) (𝒰.f j)` and uses `square_compIso_coherence`.
- `nonempty_iso_of_overlap`: on the member `pullback p (𝒰.f i)` of
  `𝒰.pullback₁ p`, the isomorphism `e i` is the composition comparison
  followed by the comparison `γ` of the transferred structure at the
  factorization `pullback.snd ≫ 𝒰.f i = pullback.fst ≫ p`. On overlaps the
  transports of `e i` and `e j` agree by `overlap_comparison`, and
  `square_compat_of_tr_eq` turns this into the gluing hypothesis. The glued
  isomorphism is `p^*M ≅ F`.

## Assembly

For every member of `Y.affineCover`, `exists_str` gives a line bundle `N i`
and `S i : Str D (𝒰.f i) (N i)`. `Str.exists_hom` gives transitions `φ i j`
compatible with the restrictions of `S i` and `S j` to the pairwise overlap,
and `cocycle_of_str` gives the cocycle condition. These form a
`LineBundleGluingData`, whose glued module `M` is a line bundle
(`gluedModule_rankOne`). `nonempty_iso_of_overlap` (with
`hom_overlap_of_compat` and `moduleIso_compatible`) gives `p^*M ≅ F`.

The theorem is split into these separate lemmas because a single proof term
exceeded the kernel's deterministic time limit.
