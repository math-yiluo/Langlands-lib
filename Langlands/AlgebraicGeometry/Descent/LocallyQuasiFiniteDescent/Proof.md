# Effective fppf descent of separated locally quasi-finite schemes

Module `Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Proof`, namespace
`Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent`. This module proves the published
statement `Langlands.AlgebraicGeometry.FppfSeparatedLocallyQuasiFiniteDescentStatement`. That
statement is Stacks Project Lemma 37.57.1 (Tag 02W8) in sheaf form: effective fppf descent of
separated, locally quasi-finite morphisms (locally of finite type, as in Stacks Tag 01TD).

## Statements

- `exists_affineChart hJ t`. Let `J` be an fppf covering sieve of `T : Over S` and `t` a point
  of `T.left`. Then there are:
  - an affine open `D ⊆ T.left`;
  - `V : Over S` with `V.left` affine;
  - `g : V ⟶ T` in `J` with `t` in the image of `g.left`;
  - `g' : V.left ⟶ D`, flat and locally of finite presentation, with `g' ≫ D.ι = g.left`.
- `ofArrows_mem_fppfTopology g hflat hlfp hsurj`: a family `g i : V i ⟶ T` (`i : I`, with `I`
  in universe `u`) of flat morphisms locally of finite presentation whose images cover
  `T.left` generates an fppf covering sieve of `T`.
- `fppfSeparatedLocallyQuasiFiniteDescent : FppfSeparatedLocallyQuasiFiniteDescentStatement.{u}`.
  Let `G` be an fppf sheaf on `Over S` and `p : G ⟶ h T`, where `h = schemeYoneda S`. Let `J`
  be an fppf covering sieve of `T`. Suppose the base change of `p` along every `g` in `J` is
  represented by a separated, locally quasi-finite morphism locally of finite type. Then `G` is
  represented by a scheme `X` over `T`: there are `x : X ⟶ T` and `e : h X ≅ G` with
  `e.hom ≫ p = h x`.

## Proof

`exists_affineChart`: the fppf topology on `Over S` is induced from the fppf topology on schemes
(`GrothendieckTopology.mem_over_iff`). So `J` contains a cover `𝒰` of `T.left` by flat
morphisms locally of finite presentation (`Scheme.exists_cover_of_mem_grothendieckTopology`).
Choose `i` and `z` with `𝒰.f i z = t`, an affine open `D ∋ t` of `T.left`, and an affine open
`W ∋ z` of `𝒰.X i` inside `(𝒰.f i)⁻¹ D`. Take `V = W` and `g = W.ι ≫ 𝒰.f i`. Then
`g' = (𝒰.f i).resLE D W` is flat and locally of finite presentation, and `g` is in `J` by
downward closure.

`ofArrows_mem_fppfTopology`: the family is a cover for the precoverage of flat, locally finitely
presented morphisms (`Scheme.Cover.mkOfCovers`). Its sieve is covering
(`Scheme.Cover.mem_grothendieckTopology`, `Sieve.overEquiv_ofArrows`).

Main theorem. For each point `t` of `T.left`, choose `D t`, `V t`, `g t` and `g' t` by
`exists_affineChart`. The hypothesis gives representing data `X' t`, `x' t` and `a' t` for the
base change of `p` along `g t`. The maps `g t` generate an fppf covering sieve of `T`
(`ofArrows_mem_fppfTopology`, indexed by the points of `T.left`). For each `t` and each point
`ξ` of `(X' t).left`, choose an affine open `U ∋ ξ`. `exists_openChart` (module
`QuasiAffineChart`) gives an open chart `b t ξ : h (Y t ξ) ⟶ G` with
`z : U ⟶ Y t ξ` such that `h z ≫ b t ξ` is the restriction of `a' t` to `U`.

Let `K = Σ t, (X' t).left` index the charts. Worker 1001's lemma
`isLocallySurjective_sigmaDesc_of_charts` (module `Covering`) shows that
`Sigma.desc b : ∐ₖ h (Y k) ⟶ G` is fppf locally surjective. The Library's `openChartGluing`
(proof of `OpenChartGluingStatement`) then gives `X : Over S` and `e : h X ≅ G`. Finally
`x : X ⟶ T` is the preimage under the fully faithful `h` of `e.hom ≫ p`, so
`e.hom ≫ p = h x` holds by construction (`Functor.map_preimage`).

The route differs from the Stacks proof. Stacks reduces to a single affine fppf covering, then
glues descended quasi-compact opens stable under the descent datum. Here no descent data
appear. The sheaf `G` is glued directly from open subfunctors that are representable by
descended quasi-affine pieces, one for each affine chart of `T` and each affine open of the
corresponding base change.
