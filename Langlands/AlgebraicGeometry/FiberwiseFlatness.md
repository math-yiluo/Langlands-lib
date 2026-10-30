# The finite-presentation fibrewise flatness criterion

`Langlands.AlgebraicGeometry.fiberwiseFlatness` proves the published proposition
`Langlands.AlgebraicGeometry.FiberwiseFlatnessStatement.{u}`. For schemes over an
arbitrary base S, a morphism f : X → Y is flat if X → S is flat and locally of
finite presentation, Y → S is locally of finite type, and every actual
residue-field base change of f is flat. The theorem has exactly this proposition
as its type.

The proof implements the stalk reduction in the first paragraph of the proof
of Stacks Theorem 37.16.2, tag [039C](https://stacks.math.columbia.edu/tag/039C),
with the structure sheaf as module. This proves the first assertion of
Stacks Lemma 37.16.4, tag [039E](https://stacks.math.columbia.edu/tag/039E).
It uses three published theorems:

- `Langlands.Algebra.localFiberwiseFlatness` supplies the local algebra
  criterion of Stacks tag 05UV.
- `Langlands.AlgebraicGeometry.stalkEssFinitePresentation` supplies essential
  finite presentation for the algebra of an actual stalk map.
- `Langlands.AlgebraicGeometry.fiberStalkFlatness` transfers flatness of the
  actual scheme fibre morphism to the required tensor-product module.

For x in X, put y = f(x), s = Y.hom(y), and
R = O_{S,s}, A = O_{Y,y}, B = O_{X,x}. The proof installs R → A and A → B
as the actual stalk homomorphisms. It defines the R-algebra on B by their
composite, so `IsScalarTower R A B` follows directly.
`Scheme.Hom.stalkMap_comp` identifies this composite with the stalk map of
f.left ≫ Y.hom. The identity `Over.w f` identifies that scheme morphism
with X.hom. These identities ensure that the finite-presentation and flatness
hypotheses on X.hom give properties of the chosen R-algebra on B.

More precisely, `stalkEssFinitePresentation` applied to f.left ≫ Y.hom
gives `Langlands.Algebra.EssFinitePresentation R B`.
`LocallyOfFiniteType.stalkMap` applied to Y.hom gives
`Algebra.EssFiniteType R A`.
`Flat.stalkMap` applied to f.left ≫ Y.hom gives `Module.Flat R B`.
The local homomorphism instances for R → A and A → B are the ones for
the actual scheme stalk maps.

Write k = `IsLocalRing.ResidueField R` and F = A tensor_R k.
The fibre hypothesis at s is precisely flatness of
`((Over.pullback (S.fromSpecResidueField s)).map f).left`.
`fiberStalkFlatness` turns it into `Module.Flat F (F tensor_A B)`.
This imported bridge proves the conclusion using compatible localizations of
affine fibre section rings. The present proof uses that theorem directly;
it does not construct isomorphisms between fibre stalks and quotient rings.

Now apply `localFiberwiseFlatness` to R → A → B with M = B, specializing
its four independent universes to u. The ring B, as a module over itself,
is finitely presented and nontrivial, as required by the criterion.
Its scalar actions and scalar towers are induced by the installed stalk
algebras. The criterion gives essential finite presentation and R-flatness
of A, and A-flatness of B. The proof selects the last conclusion.
Since x was arbitrary, `Flat.of_stalkMap` concludes flatness of f.left.
All three prerequisite results are supplied by imported theorems.

The implementation is an assembly of these established local results and
Mathlib's stalk criterion for flatness. The statement module and its imports
are preserved. The resulting theorem covers the arbitrary-base scope of the
published statement.

The registered originals are `stacks-fiberwise-isogeny-2026-10-22`,
folder content SHA256
`db82f1556e926672cc2278329e279f7fcaceb540c23e323a7c266a6a6b1f0dca`,
retained `039E.html`, Lemma 37.16.4, statement and proof; and
`stacks-algebra-flatness-criteria-2026-10-22`, folder content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
retained `039C.html`, Theorem 37.16.2, first proof paragraph, and `05UV.html`,
Lemma 10.128.9. The imported proof modules explain their respective
finite-presentation, fibre-flatness and local algebra arguments.
