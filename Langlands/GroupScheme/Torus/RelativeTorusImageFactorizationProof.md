# Proof of the relative torus image factorization

`Langlands.GroupScheme.relativeTorusImageFactorization` proves
`Langlands.GroupScheme.RelativeTorusImageFactorizationStatement.{u}` for every
universe `u`. The type of the theorem is the statement constant itself, with no
added hypothesis. The statement pair is imported unchanged.

## Lean proof

The proof introduces the scheme `S`, the commutative group scheme `T`, the group
scheme `G`, the homomorphism `f : T.toGrp ⟶ G` and the three hypotheses: `T` is
a torus (`hT`), `G` is affine over `S` (`hG`) and `G` is locally of finite
presentation over `S` (`hfp`).

The Library theorem `Langlands.GroupScheme.RelativeTorusImage.exists_factorization`
(module `Langlands.GroupScheme.Torus.RelativeTorusImage`) takes the affineness
and local finite type of `G.X.hom` as instance arguments, the torus hypothesis
explicitly, and returns the same conclusion. The proof makes `hG` and `hfp`
local instances with `have`. Mathlib's instance
`LocallyOfFinitePresentation f → LocallyOfFiniteType f`
(`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`) then supplies local
finite type. The conclusion of `exists_factorization hT f` is syntactically the
conclusion of the statement: a commutative group scheme `D`, homomorphisms
`π : T.toGrp ⟶ D.toGrp` and `j : D.toGrp ⟶ G`, with `D` a torus, `j` a closed
subgroup inclusion, the underlying morphism of `π` flat, surjective and locally
of finite presentation, and `π ≫ j = f`. Only the name of the bound inclusion
differs (`j` there, `ι` in the statement).

## What the imported theorem does

`exists_factorization` takes `D` to be the schematic image of `f` with the group
structure inherited from `G` and commutativity inherited from `T`. The map `π`
is the canonical projection onto the image and `j` is its closed inclusion. On
an étale splitting cover of `T`, the local split-torus factorization gives split
tori as images. Comparison with these charts gives flatness and surjectivity of
the projection by descent and shows that `D` is a split torus on the same cover.
Local finite presentation of `π` follows because `T` and `D` are smooth over
`S`. The companion Markdown of `RelativeTorusImage` describes this route in
detail.

## Relation to the source

The statement's Markdown derives the result from SGA 3, Exposé IX, Théorème 6.8
with its N.B. (Remarque 6.6.1) and Exposé X, Corollaire 4.5: the image is the
quotient `T/Ker u`, a group of multiplicative type that is a torus. The Lean
proof does not pass through the kernel or through multiplicative-type groups.
It builds the image as a schematic image and checks the torus property on an
étale splitting cover of `T`. Only the affineness and local finite type of `G`
are used. The local finite presentation hypothesis serves solely to give local
finite type.

## Checks

The module compiles with 0 errors and 0 warnings. The theorem has universe
parameter `u` and uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
