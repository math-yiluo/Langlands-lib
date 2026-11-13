# Gluing a Zariski sheaf from quasi-projective open pieces on locally noetherian tests

Authors: Worker 5705.

Worker 5705 wrote the Lean file and this description for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705). The proposition is the
gluing step of the Kleiman-style construction of the Picard scheme in that
task. A Zariski sheaf on schemes over a noetherian affine base is
decomposed by base-change-compatible opens into pieces. Each piece is
represented by a quasi-projective scheme, and the conclusion is that the
sheaf is represented on noetherian affine tests by a scheme that is locally
of finite presentation and has finite affine neighbourhoods. The conclusion
has exactly the form of
`Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardNoetherianTestsStatement`.

The module states this proposition only; it does not prove it.

## Statement

The module defines one declaration,
`Langlands.AlgebraicGeometry.Picard.NoetherianOpenPiecesGluingStatement`,
with the single universe parameter `u`. It is a proposition (`def … : Prop`).
It imports the Library module
`Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardNoetherianTestsStatement`
for the inclusion `noetherianAffineOverι S` of the full subcategory of
`Over S` whose objects have affine noetherian source.

### Data and hypotheses

Let `A : Type u` be a noetherian commutative ring, `S = Spec (CommRingCat.of A)`.

- `F : (Over S)ᵒᵖ ⥤ Type (u + 1)` is a presheaf on all schemes over `S`,
  assumed to be a sheaf for the Zariski topology on `Over S`
  (`Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F`).
- `κ : Type` is an index type.
- `V T ξ c m : T.left.Opens` is an open of `T` for every `T : Over S`,
  `ξ ∈ F(T)`, `c : κ` and `m : ℕ`.
- `Q c m : Over S` is a scheme over `S` for every `c : κ` and `m : ℕ`.
- `β c m : uliftYoneda.{u + 1}.obj (Q c m) ⟶ F` is a natural transformation:
  a natural map from `S`-morphisms `T ⟶ Q c m` to `F(T)`, lifted to universe
  `u + 1`. By Yoneda it is the same as an element of `F(Q c m)`.

The hypotheses are as follows. Here `T` and `T'` always range over objects of
`Over S` whose underlying scheme is locally noetherian (Mathlib's
`IsLocallyNoetherian`). Nothing is assumed about `V` or `β` at other tests.

1. **Base change.** For every morphism `h : T' ⟶ T` in `Over S`, every `ξ`,
   `c` and `m`: `V T' (F.map h.op ξ) c m = h.left ⁻¹ᵁ V T ξ c m`.
2. **Shape.** For every `T` and `ξ ∈ F(T)`:
   - `V T ξ c m ≤ V T ξ c (m + 1)` for all `c, m` (increasing in `m`);
   - `V T ξ c m` and `V T ξ c' m'` are disjoint when `c ≠ c'`, for all `m, m'`;
   - `⨆ c m, V T ξ c m = ⊤` (the opens cover `T`).
3. **Quasi-projectivity of the pieces.** For every `c, m` there are `n : ℕ` and
   a morphism `i : (Q c m).left ⟶ ProjectiveSpace A n` that is an immersion
   (Mathlib's `IsImmersion`) and satisfies
   `i ≫ projectiveSpaceToSpec A n = (Q c m).hom`. `ProjectiveSpace A n` and
   `projectiveSpaceToSpec` are the Library's projective space over `A` and
   its structure morphism.
4. **Representability of the pieces.** For every `c, m` and every locally
   noetherian `T`, the map `(β c m).app (op T)` is injective, and its image
   is exactly the set of `ξ ∈ F(T)` with `V T ξ c m = ⊤`.

### Conclusion

There is `P : Over S` such that

- `P.hom` is locally of finite presentation (`LocallyOfFinitePresentation`);
- `P.left` has finite affine neighbourhoods
  (`PointTopology.HasFiniteAffineNeighborhoods`: every finite set of points
  lies in an affine open);
- there is a natural isomorphism, on the full subcategory of `Over S` of
  affine noetherian schemes, between the functor of points of `P` (lifted
  to `Type (u + 1)` by `uliftFunctor`) and `F`:
  ```lean
  (noetherianAffineOverι S).op ⋙ yoneda.obj P ⋙ uliftFunctor.{u + 1} ≅
    (noetherianAffineOverι S).op ⋙ F
  ```

This is word for word the conclusion of
`NoetherianIntegralFibrePicardNoetherianTestsStatement`, with `F` in place of
the Picard class sheaf `RelativePicard.classSheafPresheaf f`.

## Source and derivation

### Original sources

1. The Stacks Project, Chapter 26, Section 26.15, Lemma 26.15.4,
   [Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ), registered as
   `stacks-open-chart-representability-2026-11-01` (folder
   `Stacks Project - Open chart representability (HTML snapshot 2026-11-01)`,
   files `01JJ.html` and the reading aid `01JJ.txt`; the full lemma, proof
   and comments were read). Let `F` be a set-valued contravariant functor on
   schemes that satisfies the Zariski sheaf property. Suppose it is covered
   by a family of representable subfunctors `F_i ⊂ F` whose inclusions are
   representable by open immersions. Then `F` is representable. The proof
   glues the representing schemes `X_i` along the opens
   `U_ij ⊂ X_i` where the universal family lies in `F_j`.
2. S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1 (2005),
   registered as `kleiman-2005-picard-scheme-arxiv-math0504020v1`, proof of
   Theorem 4.8, pp.28–29. Kleiman shows that `T^φ ⊂ T`, the open where the
   Hilbert polynomial of `L⁻¹` is `φ`, represents `P^φ ×_P T`. The `T^φ`
   are disjoint and cover `T`, so by EGA 0 4.5.4 `P` is the disjoint union
   of the `P^φ` once these are representable (p.29). Each `P^φ` is then
   represented as an increasing union of open quasi-projective `S`-schemes
   `P^φ_m` (pp.29–30). Kleiman's standing convention (p.15) is that all
   schemes, in particular all test schemes, are locally noetherian.

### Relation of the Lean proposition to the sources

The proposition is a **derived** special case of Tag 01JJ, in the form that
Kleiman's p.29 argument needs. It is not a verbatim statement of either
source. The differences are:

- **Explicit opens.** Instead of subfunctors representable by open
  immersions, the pieces are given by explicit opens `V T ξ c m` of each
  test. Base change (hypothesis 1) is what makes
  `{ξ | V T ξ c m = ⊤}` a subfunctor whose inclusion is representable by the
  open immersion `V T ξ c m ⊂ T`. This matches how Kleiman produces his
  pieces (the opens `T^φ` on p.28 and the nested opens on p.29).
- **Index shape `κ × ℕ`.** The covering family is indexed by `(c, m)`,
  disjoint in `c` and increasing in `m`, matching Kleiman's `P^φ_m`
  (disjoint in `φ`, nested in `m`). Tag 01JJ allows an arbitrary index set
  with arbitrary overlaps.
- **Locally noetherian tests.** The hypotheses on `V` and `β` are imposed
  only on locally noetherian `S`-schemes, Kleiman's convention (p.15).
  Tag 01JJ quantifies over all schemes. Here only the Zariski sheaf property
  of `F` is required for all tests. Its conclusion is likewise restricted,
  to noetherian affine tests.
- **Finiteness conclusions.** Tag 01JJ asserts representability only. The
  two further properties of `P` follow from the hypotheses on the pieces as
  follows:
  - Each `Q c m` is quasi-projective over the noetherian ring `A`, so it is
    of finite type over `A`, hence locally of finite presentation. `P` is
    covered by open copies of the `Q c m`, so it is locally of finite
    presentation over `S`.
  - Each `Q c m` has finite affine neighbourhoods. The Library proves this as
    `Langlands.AlgebraicGeometry.PointTopology.hasFiniteAffineNeighborhoods_of_projectiveImmersion`.
    `P` is a disjoint union, over `c`, of increasing unions of open copies
    of the `Q c m`. Any finite set of points therefore lies in finitely many
    of the components and, within each component, in a single `Q c m`.
    Compare the Library's
    `hasFiniteAffineNeighborhoods_of_disjoint_directed_ample_openCover`.
  These correspond to the form of Kleiman's Theorem 4.8(2) (pp.27–28):
  `Pic` is a disjoint union of open subschemes, each an increasing union of
  open quasi-projective `S`-schemes.
- **Quasi-projective.** Quasi-projectivity is written out as an immersion
  into the Library's `ProjectiveSpace A n` over `S`, the convention of the
  Library's `hasFiniteAffineNeighborhoods_of_projectiveImmersion`. Mathlib's
  `IsImmersion` is a preimmersion (a homeomorphism onto its image with
  surjective maps on stalks) whose image is locally closed. Since
  `ProjectiveSpace A n` is noetherian, the source of such an immersion is a
  noetherian space, so the immersion is quasi-compact and `Q c m` is of finite
  type over `A`.

### Intended proof

The intended proof follows Tag 01JJ, simplified by the index shape. Let
`ξ_{c,m} ∈ F(Q c m)` be the element corresponding to `β c m` (the image of
`𝟙 (Q c m)`).

1. **Transition maps.** Each `Q c m` is noetherian. By hypothesis 4,
   `V (Q c m) ξ_{c,m} c m = ⊤`, so by monotonicity `ξ_{c,m}` lies in the
   image of `β c (m + 1)`. This gives `j : Q c m ⟶ Q c (m + 1)`. The open
   `V (Q c (m+1)) ξ_{c,m+1} c m` and `Q c m` represent the same functor
   `{ξ | V T ξ c m = ⊤}` on locally noetherian tests (by hypotheses 1, 2
   and 4). Both are locally noetherian, so by Yoneda, `j` is an isomorphism
   onto that open.
2. **Gluing.** `P_c` is the increasing union of the `Q c m` along the open
   immersions `j`, and `P = ∐_c P_c`. The elements `ξ_{c,m}` glue to
   `ξ_P ∈ F(P)` by the Zariski sheaf property.
3. **Bijection on noetherian affine tests.** Let `T` be noetherian and
   affine and `ξ ∈ F(T)`. The disjoint opens `T_c = ⋃_m V T ξ c m` cover the
   quasi-compact `T`. So only finitely many are nonempty, each is closed and
   open, and each equals `V T ξ c m_c` for some `m_c`. By hypothesis 4
   applied to `T_c`, `ξ|_{T_c}` comes from a unique `T_c ⟶ Q c m_c`. These
   maps glue to the unique `T ⟶ P` pulling `ξ_P` back to `ξ`.

## Conventions and scope

- `F` is valued in `Type (u + 1)`, since the intended `F`, the Picard class
  sheaf `RelativePicard.classSheafPresheaf f`, takes values in that
  universe. `β` therefore uses `uliftYoneda.{u + 1}`.
- `κ : Type` is a small index type, as in the companion statement
  `PicardHilbertPolynomialPiecesStatement` of Task 5705 (Kleiman's pieces are
  indexed by pairs of rational polynomials).
- The intended consumer is the assembly proof of
  `NoetherianIntegralFibrePicardNoetherianTestsStatement` in Task 5705. There,
  `F` is the Picard class sheaf, `V` comes from the open pieces of
  `PicardHilbertPolynomialPiecesStatement`, and `Q c m` from the quotient
  of an open of the divisor scheme by the linear-system equivalence relation.
  This describes intended use only; this module imports none of those
  statements except the one supplying `noetherianAffineOverι`.
- The Library's `Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartGluingStatement`
  is a different adaptation of Tag 01JJ, with fppf sheaves, all tests and
  locally surjective charts. It does not cover the locally noetherian
  hypotheses or the finiteness conclusions used here.
