# Split tori and their normalizers under a surjection with central kernel

Module `Langlands.GroupScheme.CentralSurjection.TorusImage`, namespace
`Langlands.GroupScheme`. Internal helper for the comparison of buildings along
a surjection with central kernel (Kaletha–Prasad Axiom 4.1.1). It imports
`Langlands.GroupScheme.CentralSurjection.DerivedMap`. Author: Worker 230.

Throughout, `k` is a field and all group schemes are over `Spec k`.
`CommGroupScheme.groupHom` turns a homomorphism of commutative group schemes
into a homomorphism of group schemes.

## The image of a maximal split torus

`exists_maximalSplitTorus_image`. Let `G`, `G'` be connected reductive and
`f : G ⟶ G'` surjective on underlying schemes with central kernel. For every
maximal split torus `i : S ⟶ G` there are a commutative group scheme `S'`, a
maximal split torus `i' : S' ⟶ G'` and `fS : S ⟶ S'` with
`i ≫ f = groupHom fS ≫ i'`, where `groupHom fS` is flat, surjective and locally
of finite presentation.

Proof. The published `IsSplitTorus.fppfImage` gives the closed split image of
`i ≫ f` together with an fppf projection onto it. The map `f` is flat
(`flat_of_surjective`, as `G'` is smooth) and locally of finite presentation
(finite type over the locally noetherian `G'`). The published
`centralSurjectionMaximalSplitTorusImage` (Borel–Tits 2.20(ii)) then shows the
image is a maximal split torus.

## Normalizer points under an fppf torus image

`IsFppfTorusImage q i j p` is a structure: for `q : G ⟶ H`, `i : T ⟶ G`,
`j : T' ⟶ H` and `p : T ⟶ T'`, it asserts that `j` is a closed subgroup,
`groupHom p ≫ j = i ≫ q`, and `groupHom p` is flat, surjective and locally of
finite presentation. No property of `q` is assumed.

Given `h : IsFppfTorusImage q i j p`:

- `h.conjugate_range_le`: if `n` normalizes `i` (`IsNormalizingPoint i n σ`),
  the conjugate `j ≫ inner(q(n))` has range in the range of `j`;
- `h.normalizerEnd n`, `h.normalizerAut n : T' ≅ T'`: conjugation by `q(n)`
  restricted to `T'`, for `n ∈ normalizerPoints i`, with
  `h.isNormalizingPoint_normalizerAut n : IsNormalizingPoint j (n ≫ q) _`;
- `h.normalizerPointsMap : normalizerPoints i →* normalizerPoints j`, with
  `h.normalizerPointsMap_apply n = n ≫ q.hom.hom` (by `rfl`);
- `h.map_mem_normalizerPoints`: `n ∈ normalizerPoints i` implies
  `rationalPoints.map q n ∈ normalizerPoints j`.

The proofs are those of the published `Langlands.GroupScheme.Adjoint.Normalizer`
for the adjoint quotient, which use only the fields above. A point `y` of `T'`
is pulled back along the fppf map `p`. There it becomes a point of `T`, and
`IsNormalizingPoint` moves it inside `T`. The square
`p ≫ j ≫ inner(q(n)) = σ ≫ p ≫ j` then shows that the conjugate lies in the
range of `j` after the pullback. Fpqc descent
(`SubgroupFunctor.mem_range_of_comp_mem_range`) removes the pullback. The
factorization through `j` (`IsRepresentedBy.factorHom`) gives the endomorphism
`normalizerEnd n`, and `normalizerEnd n⁻¹` is its inverse.

## The derived maximal split tori

`exists_derivedTorus_isogeny`. The setting:

- `G`, `G'` connected reductive, with derived subgroups `d : D ⟶ G` and
  `d' : D' ⟶ G'`;
- `f : G ⟶ G'` surjective with central kernel;
- split subtori `i : S ⟶ G` and `i' : S' ⟶ G'`, with `fS : S ⟶ S'` and
  `i ≫ f = groupHom fS ≫ i'`;
- maximal split tori `j : T ⟶ D` and `j' : T' ⟶ D'`, with `e : T ⟶ S`,
  `e' : T' ⟶ S'`, `j ≫ d = groupHom e ≫ i` and `j' ≫ d' = groupHom e' ≫ i'`.

Then there is `t : T ⟶ T'` with:

- `j ≫ f_D = groupHom t ≫ j'`, where `f_D = hd.map hd' f`;
- `t ≫ e' = e ≫ fS`;
- `IsIsogeny (groupHom t)`: `groupHom t` is finite, flat and surjective.

Proof. The image of `T` in `G'` is `T ⟶ S ⟶ S'`, and the image of `T'` lies in
`S'`. Since `S'` is commutative and `d'` is a monomorphism, the points of
`j ≫ f_D` commute with those of `j'`. The published
`IsMaximalSplitTorus.exists_factor_of_commute` factors `j ≫ f_D` as `t₀ ≫ j'`.
Let `p ≫ inc` be the closed split image of `t₀` in `T'` (`IsSplitTorus.fppfImage`).
`f_D` is a central isogeny (`IsDerivedSubgroup.isCentralIsogeny_map`). `D` and
`D'` are connected reductive (`derivedSubgroupSemisimple`). So
`centralSurjectionMaximalSplitTorusImage` applied to `f_D` makes
`inc ≫ j'` a maximal split torus of `D'`. Maximality, applied to its
factorization through `j'`, makes `inc` an isomorphism. Hence `t₀ = p ≫ inc`
is flat and surjective. It is finite by `IsFinite.of_comp`, because
`t₀ ≫ j' = j ≫ f_D` is finite and `j'` is separated. The identity
`t ≫ e' = e ≫ fS` is checked after the monomorphism `i'`.

## Provenance

This is internal content, supporting Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Axiom 4.1.1 (printed pp.157–158). That a surjection with
central kernel maps a maximal split torus onto a maximal split torus is
Borel–Tits 2.20(ii), used here through the Library's
`centralSurjectionMaximalSplitTorusImage`. The normalizer and derived-torus
statements are standard consequences, formalized as described above.
