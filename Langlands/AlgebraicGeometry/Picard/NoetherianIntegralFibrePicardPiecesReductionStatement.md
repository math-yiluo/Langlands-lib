# The Picard scheme on noetherian affine tests from its Hilbert-polynomial pieces

Authors: Worker 5705.

`Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardPiecesReductionStatement.{u}`
is the proposition

```lean
ProperAmpleClosedImmersionBySectionsStatement.{u} →
  PicardHilbertPolynomialPiecesStatement.{u} →
    PicardHilbertPiecesRepresentabilityStatement.{u} →
      ProperFlatIntegralSheafClassTwistStatement.{u} →
        NoetherianOpenPiecesGluingStatement.{u} →
          NoetherianIntegralFibrePicardNoetherianTestsStatement.{u}
```

in module
`Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardPiecesReductionStatement`. All
six names are existing Prop-valued definitions in namespace `Langlands.AlgebraicGeometry.Picard`,
used unchanged at the same universe `u`. This unit only defines the proposition. It proves none
of the six propositions; it says only that the last follows from the first five.

## The six propositions

In each item, `S = Spec R` for a commutative ring `R : Type u`. "Noetherian" means
`IsNoetherianRing`.

1. `ProperAmpleClosedImmersionBySectionsStatement` (first hypothesis, "K1"). If `R` is
   noetherian and `f : X ⟶ S` is proper, and `X` has an ample line bundle, then there is an
   invertible module `M` on `X` with `Scheme.Modules.ClosedImmersionBySections M f`: finitely
   many global sections of `M` define a closed immersion of `X` into a finite projective space
   over `R`.
2. `PicardHilbertPolynomialPiecesStatement` (second hypothesis). Let `R` be noetherian, let
   `f : X ⟶ S` be proper, flat and geometrically integral, and let `𝓛X` be an invertible
   module with `ClosedImmersionBySections 𝓛X f`. Then there are an index type `κ`, polynomials
   `θ c m` and opens `U T s L c m` of `T`, for every `s : T ⟶ S`, every module `L` on
   `pullback f s` and every `c : κ`, `m : ℕ`. On locally noetherian `T` and invertible `L`
   they satisfy five properties:
   - invariance under `L ↦ L ⊗ g^* N`;
   - base change;
   - increasing in `m`, disjoint in `c`, covering `T`;
   - `H¹ = 0` and `H⁰ ≠ 0` for `L(m)` on every fibre over a whole piece;
   - the Hilbert polynomial `θ c m` for the divisors in the linear system of `L(m)` over
     noetherian affine tests.
3. `PicardHilbertPiecesRepresentabilityStatement` (third hypothesis). Take `f` and `𝓛X` as in
   item 2, and assume moreover that `f` has a section. Let `κ`, `θ` and `U` satisfy the first,
   second, fourth and fifth properties of item 2. Then for every `(c, m)` there are an
   H-quasi-projective `Q : Over S` and a map
   `β : uliftYoneda.{u + 1}.obj Q ⟶ RelativePicard.classSheafPresheaf f`. On every locally
   noetherian `T`, `β` is injective. Its image contains the class of a line bundle `L` on
   `T ×_S X` exactly when `U` is all of `T` for `L` transported to `X ×_S T`.
4. `ProperFlatIntegralSheafClassTwistStatement` (fourth hypothesis). Let `f : X ⟶ S'` be
   proper, flat, locally of finite presentation and geometrically integral, with a section,
   over any scheme `S'`. Then every element of the fppf Picard class sheaf at an `S'`-scheme
   `T` is the class of a line bundle on `T ×_{S'} X`. Two line bundles have the same class
   exactly when they differ by the pullback of an invertible module on `T`.
5. `NoetherianOpenPiecesGluingStatement` (fifth hypothesis). Let `R` be noetherian and let `F`
   be a Zariski sheaf on `S`-schemes. Suppose `F` has opens `V T ξ c m`, defined for every
   element `ξ`, with these properties on locally noetherian tests:
   - compatible with base change;
   - increasing in `m`, disjoint in `c`, covering;
   - each piece `{ξ | V T ξ c m = T}` is represented on locally noetherian tests by an
     `S`-scheme `Q c m` that immerses into a finite projective space over `R`.

   Then some `S`-scheme `P` is locally of finite presentation, has finite affine
   neighbourhoods, and represents `F` on noetherian affine tests.
6. `NoetherianIntegralFibrePicardNoetherianTestsStatement` (conclusion). Let `R` be noetherian
   and `f : X ⟶ S` proper, flat and geometrically integral, with a section. Assume `X` has an
   ample line bundle. Then there is `P : Over S` with three properties:
   - `P` is locally of finite presentation;
   - `P` has finite affine neighbourhoods;
   - `P` has a natural isomorphism
     between its functor of points (lifted to `Type (u + 1)`) and
     `RelativePicard.classSheafPresheaf f`, both restricted along `noetherianAffineOverι S`
     to noetherian affine `S`-schemes.

## Provenance

Internal. The implication is the assembly step of the work task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705). It adds no mathematics of its own: the
geometric content lies in the five hypotheses, whose Markdown cites the sources. It is the
order of argument in the proof of Theorem 4.8 in S. L. Kleiman, *The Picard scheme*, arXiv
math/0504020v1 (2005), pp.28–31 (registered as
`kleiman-2005-picard-scheme-arxiv-math0504020v1`):

- an ample line bundle on `X` gives the projective embedding `O_X(1)` (first hypothesis);
- the Picard sheaf is the disjoint union of the strata `P^φ`, one for each Hilbert
  polynomial `φ`, and each `P^φ` is the increasing union of its open pieces `P^φ_m`
  (p.29; second hypothesis: disjoint in the index `c`, increasing in `m`);
- each piece is representable by a quasi-projective scheme (third hypothesis);
- the pieces glue to the Picard scheme (fifth hypothesis, Kleiman's reference to EGA 0
  4.5.4).

The fourth hypothesis (Kleiman's Theorem 2.5 and Exercise 3.11) gives, for each element of the
Picard sheaf, a line bundle whose pieces define the pieces of that element. A Lean proof of the
implication is a separate unit.
