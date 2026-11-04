# Solvable radicals of a group with a rational Levi decomposition

Author: Worker 1131.

This internal helper module proves that the solvable radical of a rational
Levi subgroup determines the solvable radical of the ambient group: it is the
inverse image of the Levi radical under the Levi retraction. Proved over the
ground field and over its algebraic closure, this gives a geometric solvable
radical of the ambient group. The module also proves that a parabolic of a
connected reductive group has a rational Levi subgroup, assuming two published
structure statements. Everything is in the namespace
`Langlands.GroupScheme.LeviPreimageRadical`, except two theorems in the
namespaces of the predicates `IsRationalLeviSubgroup` and
`IsParabolicSubgroup`.

All fields `K` and `k` are arbitrary fields in universe `u`. No perfectness,
splitness or characteristic assumption is made. Subgroup containment,
normality and greatestness refer to the represented subgroup functors on
every test scheme over the base, including nonreduced ones.

## Normality of a schematic image

`isNormal_range_imageInclusion` takes group schemes `P`, `L`, `H` over
`Spec K`, homomorphisms `l : L → P`, `q : P → L`, `h : H → P` with `L` and
`H` affine over the base, `l ≫ q = 𝟙 L`, and normal range of `h` in `P`. It
concludes that the inclusion of the schematic image of `h ≫ q` into `L` has
normal range.

Proof. Let `p` and `i` be the projection onto the schematic image and its
closed inclusion into `L`. Take the conjugation morphism
`g(x, z) = x · i(z) · x⁻¹` from `L × image` to `L`. Normality of the range of
`h` applied to the pair `(l ∘ fst, h ∘ snd)` on `L × H` gives a morphism `y` to
`H` with `h(y) = l(x) · h(z) · l(x)⁻¹`. Applying `q` and using `q ∘ l = id`
shows `g ∘ (L × p) = i ∘ p ∘ y`. Since `L × p` is scheme-theoretically dominant
and `i` is a closed immersion, `g` factors through the image
(`exists_over_factor_of_schematic_precomp`). The factorization gives the
required conjugate on every test scheme.

## Images of solvable groups

`isSolvableGroupScheme_of_surjective` states that a homomorphism `f : H → D`
of group schemes locally of finite type over `Spec K`, surjective on
underlying schemes, carries `IsSolvableGroupScheme H` to
`IsSolvableGroupScheme D`. Proof: base change to `AlgebraicClosure K` keeps
`f` surjective; every rational point of the base-changed `D` lifts
(`DominantHom.rational_lift`); so the induced map of rational point groups is
a surjective homomorphism from a solvable group.

## The inverse image of a radical

`isSolvableRadical_preimage` takes homomorphisms `l : L → P`, `q : P → L`,
`u : U → P` and `c : C → L` over `Spec K`, with these hypotheses:

- `P` and `L` are affine over the base, and `L` is locally of finite type;
- the morphism of schemes underlying `q` is smooth and geometrically
  connected, and `l ≫ q = 𝟙 L`;
- every algebraic-closure point of `P` killed by `q` is the image under `u`
  of an algebraic-closure point of `U`;
- the group of algebraic-closure points of `U` is solvable;
- `IsSolvableRadical c`.

It concludes `IsSolvableRadical (SubgroupPreimage.inclusion q c)`: the inverse
image of `C` under `q` is a solvable radical of `P`.

Proof. Closedness, smoothness, connectedness and normality of the inverse
image come from the published `SubgroupPreimage` lemmas. These use the
smoothness and geometric connectedness of `q` and the corresponding properties
of `c`. For solvability, consider the group of algebraic-closure points of
the inverse image. Projection to `C` has kernel mapping injectively into the
image of `U`'s points, so the kernel is solvable. The points of `C` form a
solvable group by `SolvableFieldExtensionProof.allPoints_isSolvable`. So the
group is an extension of solvable groups.

For greatestness, let `h : H → P` be a closed subgroup with `H` smooth,
connected, solvable and of normal range. The schematic image of `h ≫ q` in
`L` is closed and smooth (`HomImage`) and connected. It is solvable by the
preceding lemma applied to the surjective projection, and normal by the first
lemma. Greatestness of `c` puts its range inside the range of `c`, so the
range of `h` lies in the inverse image.

## Rational Levi subgroups

`isSolvableRadical_of_range_eq` transfers `IsSolvableRadical` from `r` to any
closed subgroup `r'` of the same ambient group with smooth, connected,
solvable source and the same range functor.

`IsRationalLeviSubgroup.exists_isGeometricSolvableRadical` assumes
`IsRationalLeviSubgroup l` for `l : L → P` and `IsGeometricSolvableRadical c`
for `c : C → L`. It concludes that some `r : R → P` satisfies
`IsGeometricSolvableRadical r`.

Proof. The Levi predicate supplies a geometric unipotent radical
`U → P` whose multiplication with `l` is an isomorphism. Let `q` be the
published `leviRetraction`, which is smooth and geometrically connected, with
`l ≫ q = 𝟙 L` and kernel equal to the range of `U` on every test scheme. The
points of `U` form a solvable group because `U` is unipotent. The preceding
theorem gives a solvable radical `R = q⁻¹(C)` of `P` over the ground field.

Over `AlgebraicClosure k`, apply the same theorem to the base changes of
`l`, `q`, the radical inclusion of `U` and `c`. The kernel condition is
transported by `baseChangePointsEquiv`, unipotence comes from the
algebraic-closure part of the geometric unipotent radical predicate, and the
algebraic-closure radical of `C` is the second part of the hypothesis on `c`.
This proves that the inverse image of the base-changed `C` is a solvable
radical of the base-changed `P`. Its range functor equals that of the
base-changed inclusion of `R` (`range_baseChangeHom`, `comap_baseChange`).
The base change of `R` is closed, smooth, connected and solvable. So
`isSolvableRadical_of_range_eq` makes the base change of `R` the solvable
radical over the algebraic closure. No descent argument is needed.

## Rational Levi subgroups of parabolics

`IsParabolicSubgroup.exists_isRationalLeviSubgroup` assumes the published
statements `ParabolicDynamicStatement.{u}` (module `Absolute.BorelStatement`)
and `DynamicCentralizerReductiveStatement.{u}` (module
`Dynamic.CentralizerReductiveStatement`) as explicit hypotheses. It also
assumes `IsConnectedReductive G` and `IsParabolicSubgroup j` for
`j : P → G`. It concludes that some `l : L → P` satisfies
`IsRationalLeviSubgroup l`.

Proof. The first hypothesis gives a cocharacter `χ` defined over `k` with
range of `j` equal to the dynamic parabolic `P_G(χ)`. The canonical affine
representatives of the dynamic centralizer `Z_G(χ)` and of the dynamic
identity-limit subgroup `U_G(χ)` (`Dynamic.Affine.centralizerHom`,
`Dynamic.Affine.unipotentHom`) factor through `j`. The second hypothesis
makes the centralizer representative connected reductive. The published
`Dynamic.isGeometricUnipotentRadical_of_centralizer` makes the factor of
`U_G(χ)` a geometric unipotent radical of `P`. Finally
`Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical` shows that the
factor of `Z_G(χ)` is a rational Levi subgroup.

The two structure statements remain hypotheses of this theorem; this module
does not prove them.

## Provenance

This module is derived internal content. Its arguments are standard group
theory, the published scheme-theoretic image, inverse-image, base-change and
Levi-retraction lemmas, and the published dynamic structure theorems. The
mathematical route is the one in the proof of Borel–Tits, *Groupes
réductifs*, Corollary 3.14, cited in the Markdown of
`Rational.ParabolicGeometricSolvableRadicalExistsStatement`: the radical of a
parabolic is built from a rational Levi subgroup and the unipotent radical.
Here it is formed as the inverse image of the Levi radical rather than as a
product with a central torus. The external content of the two structure
hypotheses is documented in their own statement Markdown. This module adds no
new citation and asserts no external structural statement.
