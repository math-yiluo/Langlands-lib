# Closed normalizers of smooth connected subgroup schemes

`Langlands.GroupScheme.smoothConnectedNormalizer` proves exactly
`Langlands.GroupScheme.SmoothConnectedNormalizerStatement.{u}` at an arbitrary
universe `u`. The statement and its imports are unchanged.

Over every scheme `S`, let `G` be a smooth affine group scheme and
`i : H ⟶ G` a closed subgroup with `H` smooth and geometrically connected
over `S`. The theorem gives a group scheme `N` and a homomorphism `j : N ⟶ G`.
`j` is a closed immersion, is locally of finite presentation, and represents
the all-test normalizer of `SubgroupFunctor.range i` in the sense of
`SubgroupFunctor.IsRepresentedBy`. No Noetherian, reducedness, field or
projectivity hypothesis is added. The theorem term applies
`SmoothNormalizer.exists_normalizer`.

## Structure of the proof

The helper modules under `Langlands/GroupScheme/SmoothNormalizer/` each have
their own Markdown with details.

1. `KrullSection`: a Krull intersection theorem along the section of a
   smooth algebra, without Noetherian hypotheses. If `b` lies in every power
   of `ker ε` for a section `ε : C → R` of a smooth `R`-algebra `C`, then
   `s * b = 0` for some `s` with `ε s = 1`. The proof descends `C` to a smooth
   algebra over a finitely generated `ℤ`-algebra and uses the diagonal model
   `C₀ ⊗ C₀` over `C₀`, so the section need not descend.
2. `OpenSubgroup`: a closed subgroup of a smooth corepresented group with
   connected fibres, cut out by a finitely generated ideal contained in every
   power of the augmentation ideal, is everything. The open locus where the
   subgroup agrees with the group contains the identity section. It is
   stable under products and inverses, by flatness of the comultiplication.
   A coset argument over residue fields shows that it is closed in every
   fibre.
3. `BaseChange`: the base change `A ⊗[R] D` corepresents a corepresented group
   functor restricted to `A`-algebras.
4. `CutOut`: for a smooth closed subgroup `Spec (B ⧸ I)` with connected
   fibres, the normalizer is cut out by an ideal of `B`. This ideal is the
   supremum of coefficient ideals along the finite projective jet modules
   `(B ⧸ I) ⧸ J ^ (n + 1)`, and it is finitely generated. A point lies in the
   normalizer exactly when both conjugates of the universal subgroup point
   vanish on `I` modulo every power of `J`, by step 2 applied over the test
   algebra.
5. `Affine`: the target over `Spec R`, through the Library's affine
   coordinates. Finite generation of the ideal gives local finite
   presentation of the closed immersion.
6. `Global`: the target over any `S`. Apply the affine case over the affine
   open cover of `S`. Glue the resulting closed subschemes of `G`, since the
   normalizer condition is local on the test scheme. Check local finite
   presentation on the cover. Then transfer the group structure to the glued
   closed subscheme.

## Source

This is the subgroup case of Brian Conrad, *Reductive group schemes* (2014),
Proposition 2.1.6, printed and one-based PDF pp.61–62, with the proof
continuing on p.63. The registered source is
`conrad-2014-reductive-group-schemes`, SHA256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`. Conrad
represents the normalizer as the intersection of the transporters of the
infinitesimal neighbourhoods of the identity, and proves density of these
neighbourhoods by Noetherian approximation and Krull's theorem. The formal
proof follows the same overall strategy. Its finiteness and density arguments
are derived: finite generation comes directly from the cut-out property, and
density uses the Krull argument of step 1 and the fibrewise coset argument of
step 2. Neither uses Noetherian approximation of the group schemes.
