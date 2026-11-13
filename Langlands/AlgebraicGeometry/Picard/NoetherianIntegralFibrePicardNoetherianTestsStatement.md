# The Picard sheaf of a pointed projective flat family with geometrically integral fibres on noetherian affine test schemes

Authors: Worker 5705.

Worker 5705 wrote the Lean file and this description for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705), after reading the cited
pages of Kleiman's survey and the cited Stacks Project results. The
proposition is the core of the Library statement
`NoetherianIntegralFibrePicardSheafAFSchemeStatement`: it keeps that
statement's hypotheses and asks for representability only on noetherian affine
test schemes. Kleiman's own theorem covers only locally noetherian test
schemes, and this proposition stays inside that range.

## Statement

The module defines two declarations in the namespace
`Langlands.AlgebraicGeometry.Picard`, each with the single universe parameter
`u`.

### `noetherianAffineOverι`

For a scheme `S : Scheme.{u}`, `noetherianAffineOverι S` is an `abbrev` for

```lean
ObjectProperty.ι (fun T : Over S => IsAffine T.left ∧ IsNoetherian T.left)
```

This is Mathlib's inclusion functor of the full subcategory of `Over S` whose
objects are the `S`-schemes `T` with `T.left` affine (Mathlib's `IsAffine`) and
noetherian (Mathlib's scheme class `IsNoetherian`: locally noetherian and
quasi-compact). For affine `T.left` this means `T.left ≅ Spec A` with `A` a
noetherian ring. Morphisms in the full subcategory are all `S`-morphisms
between such objects.

### `NoetherianIntegralFibrePicardNoetherianTestsStatement`

A proposition (`def … : Prop`) whose body is

```lean
∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of R)),
  IsProper f → Flat f → GeometricallyIntegral f →
  (∃ σ : Spec (CommRingCat.of R) ⟶ X, σ ≫ f = 𝟙 _) →
  (∃ L : LineBundle X, L.IsAmple) →
    ∃ P : Over (Spec (CommRingCat.of R)),
      LocallyOfFinitePresentation P.hom ∧
        PointTopology.HasFiniteAffineNeighborhoods P.left ∧
          Nonempty ((noetherianAffineOverι (Spec (CommRingCat.of R))).op ⋙
              yoneda.obj P ⋙ uliftFunctor.{u + 1} ≅
            (noetherianAffineOverι (Spec (CommRingCat.of R))).op ⋙
              RelativePicard.classSheafPresheaf f)
```

Write `S` for `Spec (CommRingCat.of R)`, `F = RelativePicard.classSheafPresheaf f`
and `ι = noetherianAffineOverι S`. The hypotheses are exactly those of
`NoetherianIntegralFibrePicardSheafAFSchemeStatement`: `R` is a noetherian
commutative ring in `Type u`, and `f : X ⟶ S` is

1. proper (Mathlib's `IsProper`: separated, universally closed and locally of
   finite type),
2. flat (Mathlib's `Flat`),
3. geometrically integral (Mathlib's `GeometricallyIntegral`: for every field
   `K` and every `Spec K ⟶ S` the fibre product `X ×_S Spec K` is integral),
4. with a section `σ : S ⟶ X`, `σ ≫ f = 𝟙 S`,
5. and `X` carries an ample line bundle (`LineBundle.IsAmple`, from
   `Langlands.AlgebraicGeometry.Picard.Ample`, as in EGA II 4.5.2).

Under these hypotheses the proposition asserts that there is an object `P` of
`Over S` such that

1. the structure morphism `P.hom : P.left ⟶ S` is locally of finite
   presentation (Mathlib's `LocallyOfFinitePresentation`);
2. every finite set of points of `P.left` lies in one affine open subscheme
   (`Langlands.AlgebraicGeometry.PointTopology.HasFiniteAffineNeighborhoods`);
3. there is a natural isomorphism between two functors from the opposite of the
   full subcategory of noetherian affine `S`-schemes to `Type (u+1)`:
   - `ι.op ⋙ yoneda.obj P ⋙ uliftFunctor.{u+1}`, which sends `T` to
     `ULift (T ⟶ P)`, the `S`-morphisms from `T` to `P`, lifted from `Type u`
     to `Type (u+1)`;
   - `ι.op ⋙ F`, the restriction of the fppf Picard class sheaf.

So for every noetherian affine `S`-scheme `T` there is a bijection
`Hom_S(T, P) ≅ F(T)`, natural with respect to all `S`-morphisms between
noetherian affine `S`-schemes.

`F` is the underlying presheaf of the Library sheaf `RelativePicard.classSheaf f`:
Mathlib's sheafification, for `Scheme.fppfTopology.over S` on the whole slice
`Over S` and in `Type (u+1)`, of the presheaf of isomorphism classes of line
bundles on `T ×_S X`. The sheafification is formed on all of `Over S`; only its
values on noetherian affine objects enter the proposition.

Nothing is asserted on test schemes that are not affine and noetherian, and no
group structure, universal bundle, separatedness or decomposition of `P` is
asserted. The `uliftFunctor` only matches universes: hom-sets of `Over S` lie in
`Type u`, while `F` takes values in `Type (u+1)`. The proposition proves
nothing; it is a statement definition only.

### Relation to the target statement

`NoetherianIntegralFibrePicardSheafAFSchemeStatement` asks for the same `P`
with conjunct 2 and representability of `F` on every object of `Over S`. It
does not ask for conjunct 1, so neither proposition implies the other
formally. Deriving the target from this proposition requires the extension
from noetherian affine tests to all tests (noetherian approximation, which uses
conjunct 1, and Zariski gluing), Steps 4 and 5 of the derivation in the
target's Markdown. That extension is a separate obligation; it is not part of
this proposition.

## Provenance

The proposition is derived content. Its source is Grothendieck's existence
theorem for the Picard scheme, as stated and proved in

S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1 (2005), Chapter 9 of
*Fundamental Algebraic Geometry: Grothendieck's FGA Explained*, registered
source `kleiman-2005-picard-scheme-arxiv-math0504020v1`, SHA-256
`cc14e62f0ebebb8617777651bbcd08bb7548cb9fe955f3a25bb6491c5f3beeaa`. Its PDF
page numbers equal its printed page numbers.

### What the source states

- Conventions, p.15: Kleiman works "only with locally Noetherian schemes".
  The Picard functor and its Zariski, étale and fppf sheafifications
  (Definition 2.1, p.16) are functors on locally noetherian `S`-schemes.
- Theorem 4.8 (Main), pp.27–28: "Assume `f : X → S` is projective Zariski
  locally over `S`, and is flat with integral geometric fibers. (1) Then
  `Pic_{X/S}` exists, is separated and locally of finite type over `S`, and
  represents `Pic(X/S)(ét)`. (2) If also `S` is Noetherian and `X/S` is
  projective, then `Pic_{X/S}` is a disjoint union of open subschemes, each an
  increasing union of open quasi-projective `S`-schemes."
- Theorem 2.5 (Comparison), p.18: if `O_S → f_*O_X` is an isomorphism
  universally and `f` has a section, then the maps
  `Pic_{X/S} → Pic(X/S)(zar) → Pic(X/S)(ét) → Pic(X/S)(fppf)` are
  isomorphisms.
- Lemma 2.9, p.19: if `f` has a section `g`, then for every `S`-scheme `T`
  the isomorphism classes of `g`-rigidified pairs `(L, u)` on `X_T` map
  isomorphically onto `Pic_{X/S}(T)`.
- Exercise 3.11, p.25: if `f` is proper and flat with reduced and connected
  geometric fibres, then `O_S → f_*O_X` is an isomorphism universally.

Other registered sources:

- `stacks-fibre-ampleness-affine-neighbourhood-2026-11-02` (SHA-256
  `7a654789470ca2c545023588c4949fa09b3559b6801d9ff2f7c74b826eadc3a3`, file
  `01VK.html`, Lemma 29.38.5);
- `stacks-projective-space-twists-morphisms-2026-10-26` (SHA-256
  `e21fdf382a193a228965d8a018149e752c04561e3a229faae7ead34fda0d85c5`, file
  `01W7.html`, Section 29.44, Lemma 29.44.13);
- `stacks-properties-chapter-2026-10-28` (SHA-256
  `2f5b9ba41e07dd3a888da40496e07afae6caedd550597d96313ab16db4380316`, PDF p.50,
  Lemma 28.30.5, tag 01ZY).

### Derivation

Fix `R`, `f`, `σ` and an ample `L` as in the hypotheses. This follows Steps 1,
2, 3, 6 and 7 of the derivation in the Markdown of
`NoetherianIntegralFibrePicardSheafAFSchemeStatement`, without its Steps 4
and 5.

**Kleiman's hypotheses.** Over the affine base `S`, an invertible sheaf on
`X` is ample if and only if it is `f`-ample (Stacks Lemma 29.38.5, tag 01VK).
So the proper, hence finite type, `f` is quasi-projective, and since `S` is
quasi-compact and quasi-separated, `f` is projective (Stacks Lemma 29.44.13).
With flatness and integral geometric fibres, Theorem 4.8(1) and (2) apply. Let
`P` be Kleiman's `Pic_{X/S}`.

**Conjunct 1.** By Theorem 4.8(1), `P` is locally of finite type over `S`.
Since `R` is noetherian, every finitely generated `R`-algebra is finitely
presented, so `P → S` is locally of finite presentation.

**Conjunct 2.** By Theorem 4.8(2), `P` is a disjoint union of open pieces,
each an increasing union of open quasi-projective `S`-schemes. A finite set of
points meets finitely many pieces, and in each piece lies in one member of the
increasing union. That member is quasi-projective over the affine noetherian
`S`, so it has an ample invertible sheaf (Lemma 29.38.5), and every finite set
of its points lies in an affine open (Stacks Lemma 28.30.5, tag 01ZY). A finite
disjoint union of affine opens of different pieces is affine.

**Conjunct 3.** Let `T` be a noetherian affine `S`-scheme; it is locally
noetherian, so it lies in Kleiman's test category. Geometric integrality makes
the geometric fibres reduced and connected, so by Exercise 3.11
`O_S → f_*O_X` is an isomorphism universally. Writing `Rig(T)` for the set of
isomorphism classes of `σ`-rigidified line bundles on `T ×_S X` (the Library
presheaf `RigidifiedLineBundle.classPresheaf`), there are bijections, natural in
`T`,

```
Hom_S(T, P) ≅ Pic(X/S)(ét)(T)    (Theorem 4.8(1))
            ≅ Pic_{X/S}(T)       (Theorem 2.5, with the section σ)
            ≅ Rig(T)             (Lemma 2.9).
```

The Library sheaf `F` is the fppf sheafification on all of `Over S`, not on
locally noetherian `S`-schemes as in Kleiman. To identify it with `Rig` the
derivation uses a Library result rather than Kleiman: for `f` proper, flat,
locally of finite presentation (here because `f` is of finite type over the
noetherian `S`) and geometrically integral, with a section,
`RigidifiedLineBundle.properFlatIntegralClassIso` (module
`Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralRigidifiedComparison`) is
an isomorphism `Rig ≅ F` of presheaves on all of `Over S`, whose forward map
`RigidifiedLineBundle.toClassPicardSheaf` forgets the rigidification and
sheafifies. It is built from the Library theorem `rigidifiedFppfComparison`
and `AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected`
(Step 3 of the target's derivation). Restricting to noetherian affine `T` and
composing gives conjunct 3.

**Universes.** In the proof of Theorem 4.8(2), `P` is glued from countably
many quasi-projective opens, hence from countably many spectra of finitely
generated `R`-algebras, so an isomorphic copy of `P` exists in `Scheme.{u}`.

### Comparison with the source

Compared with Theorem 4.8, the proposition adds a section and a noetherian
affine base, restricts the test schemes to noetherian affine ones (inside
Kleiman's locally noetherian range), and keeps only three consequences:
local finite presentation of `P` (from local finite type over a noetherian
base), the finite-set affine property (from the decomposition in part (2)),
and representability. It omits separatedness and the decomposition itself.
It uses the fppf sheaf `F` of the Library rather than Kleiman's étale sheaf;
on these test schemes the two agree by Theorem 2.5 and the Library comparison
above. No source-specific errata note was found in the Library's
`notes/errata/` directory.

## Future proof obligations

A proof must construct, for every such `R`, `f`, section and ample bundle, an
actual `P : Over S` in `Scheme.{u}` with conjuncts 1 and 2, and a natural
isomorphism with `F` on noetherian affine tests. Following Kleiman's proof of
Theorem 4.8 it needs the Hilbert scheme of `X/S`, the openness of relative
effective divisors in it (Kleiman Theorem 3.7), linear systems as projective
bundles (Kleiman Theorem 3.13), the quotient construction of Kleiman Lemma 4.9,
and the decomposition by Hilbert polynomials (pp.28–29). None of these is a
premise of the proposition, and the proposition has not been proved.
