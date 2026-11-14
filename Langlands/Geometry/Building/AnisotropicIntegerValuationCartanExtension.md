# Affine Cartan extensions for anisotropic groups from a Galois-stable chamber

Module `Langlands.Geometry.Building.AnisotropicIntegerValuationCartanExtension`.

## Contents

The module combines the published endpoint
`exists_transitive_titsIndexCartanExtension_of_integerValuation` (module
`Langlands.Geometry.Building.IntegerValuationTitsIndexCartan`) with the irreducibility
and chamber-transitivity results of the modules
`Langlands.Geometry.Building.RelativeIrreducibleAffineRoots` and
`Langlands.Geometry.Building.AnisotropicGaloisFixedTranslations`. These two modules are
submitted together with this one. The combination proves every chamber input of the endpoint
except the Galois-stable chamber, which stays a hypothesis.

### Setting

The section variables are:

- fields `k` and `K` with `[Algebra k K]` and `[IsGalois k K]`, and
  `[Algebra K (SeparableClosure k)]` with `[IsScalarTower k K (SeparableClosure k)]`. The
  extension `K/k` may be infinite.
- a group scheme `G` over `Spec k` with `[IsAffineHom G.X.hom]` and
  `[LocallyOfFiniteType G.X.hom]`, Tits-index data `d : TitsIndexData G`, and a morphism
  `i : T.toGrp ⟶ G` from a commutative group scheme `T` over `Spec k`. Below, `T_K`, `G_K` and
  `i_K` are the published base changes along `algebraBaseMap k K`, and `[Mono i_K.hom.hom.left]`.
- an integer-valued valuation `v : Valuation K (WithZero (Multiplicative ℤ))`.
- the building data over `K`: a KP apartment `D : KPApartmentData (S := T_K) i_K
  (IntegerValuation.order v)`, `hD : KPApartmentData.GaloisStable k K i D`,
  `hGK : IsConnectedReductive G_K`, `hiK : IsMaximalSplitTorus i_K`,
  `C : CentralizerDatum i_K` and `h6 : IntegerValuation.IsOmegaCompatible v D C`. The published
  definition `KPApartmentData.integerBuildingData D hGK hiK C h6` (module
  `Langlands.Geometry.Building.GaloisFacetAction`) bundles them as
  `IntegerValuationBuildingData v G_K` with apartment `D`. Below it is written `B`. Its affine
  roots `B.affineRoots` are `D.affineRoots`, and `B.i` is `i_K`.
- `hunit : ∃ t : Kˣ, IntegerValuation.order v t = 1`: `v` has a uniformizer.
- `hstmt : RelativeRootSystemIrreducibleStatement.{u}`: the published Borel–Tits statement
  (module `Langlands.GroupScheme.Rational.RelativeRootSystemIrreducibleStatement`). It is a
  premise because its proof is not yet in the Library.
- `hG : IsAnisotropic G` and `hic : IsClosedSubgroup i`.
- `hAS : IsAlmostSimple G_K`. When `G` is absolutely almost simple this follows from the
  absolute hypothesis, but the Library has no published proof of that yet, so it stays a
  premise.
- `hiM : IsMaximalTorus i_K`: the maximal split torus `i_K` is a maximal torus, i.e. `G_K` is
  split.

### Results

Each result also takes a point `c : D.Apartment` with `hc : IsRegular D.affineRoots c`, and
`hC`: for every `σ : K ≃ₐ[k] K`, the affine automorphism
`KPApartmentData.galoisAffineAction k K i D hD σ` maps the chamber `facet D.affineRoots c` onto
itself. So `hC` says that the chamber of `c` is Galois-stable.

- `integerValuationChamberInputs_of_isAnisotropic hc hC`: `B.affineRoots` is nonempty and
  irreducible (`IsIrreducibleRoots`, KP Definition 1.3.13). There is also a `Fintype` instance
  on the simple affine roots `simpleAffineRoots B.affineRoots (facet B.affineRoots c)` for which
  `AffineCartan.IsVertexTransitive (chamberCartanMatrix B.affineRoots (facet B.affineRoots c))`
  holds. Finally `HasTransitiveSimpleRoots B.affineRoots (facet B.affineRoots c)` holds. These
  are the hypotheses `hne`, `hirr`, `hmat` and `htrans` of the published endpoint. This theorem
  does not use the two `SeparableClosure` instances.
- `exists_transitive_titsIndexCartanExtension_of_isAnisotropic hc hC`: there is a matrix
  `N : Matrix (Option d.Vertex) (Option d.Vertex) ℤ` with the following properties:
  - `N (some a) (some b) = d.cartan a b` for all absolute simple vertices `a` and `b`;
  - `N a a = 2` for all `a`;
  - `N a b ≤ 0` whenever `a ≠ b`;
  - `N a b = 0 ↔ N b a = 0`;
  - some `m : Option d.Vertex → ℤ` with `0 < m a` for all `a` satisfies
    `Matrix.vecMul m N = 0`;
  - `AffineCartan.IsVertexTransitive N`.

  These are the six conjuncts of the published target `LocalAnisotropicAffineDiagramStatement`.
- `anisotropicTitsIndexCartanExtension hc hC` (a definition): the matrix chosen by
  `Classical.choose` from the previous theorem.
- `anisotropicTitsIndexCartanExtension_spec hc hC`: the chosen matrix has these six properties.

The module does not construct the building data `D`, `C`, `h6` or a Galois-stable apartment.
It does not prove that a Galois-stable chamber exists, that `G` splits over `K`, or that `G_K`
is almost simple. All of these remain hypotheses.

## Provenance

The module is derived. It assembles the proof of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Theorem 10.3.1 (proof on printed p. 392, PDF p. 423) from imported pieces.
In that proof `G` is anisotropic over a local field `k`, `K` is the maximal unramified
extension of `k`, `C` is a `Gal(K/k)`-stable chamber of the building of `G_K`, and the matrix is
the Cartan matrix of the simple affine roots of `C`. The pieces are:

- the affine-root-system axioms of the actual affine roots
  (`IntegerValuationBuildingData.isAffineRootSystemWithRankZero_affineRoots`, published);
- the equality of their derivatives with the relative roots of `i_K`
  (`IntegerValuationBuildingData.derivativeRoots_affineRoots_of_maximalTorus`, published);
- irreducibility of the relative root system of an almost-simple group (Borel–Tits 1965,
  Corollary 5.11, through `RelativeRootSystemIrreducibleStatement` and
  `nonempty_and_isIrreducibleRoots_of_isAlmostSimple`);
- `C^Γ` has at most one point because `G` is anisotropic, so `Gal(K/k)` acts transitively on
  the simple affine roots of `C` (`KPApartmentData.chamberTransitivity_of_isAnisotropic`);
- the construction of the extended matrix on the absolute Tits-index vertices from these inputs
  (published endpoint).

Two simplifications are not in the source. The base field and `K` are arbitrary, provided
`K/k` is Galois, `v` has a uniformizer, and `i_K` is a maximal torus. The splitting of `G` over
`K`, which KP derive at the end of the same proof, is the hypothesis `hiM`.

## Proof notes

- A private theorem `relativeRoots_nonempty_of_isAlmostSimple` shows that a split maximal torus
  `j` of an almost-simple group `H` has a relative root. If not, the published
  `IsConnectedReductive.isIso_of_roots_eq_empty` makes `j` an isomorphism. Then `H` is
  commutative, because multiplication commutes on the torus and can be transported along
  `inv j`. This contradicts `IsAlmostSimple.noncommutative`. The argument is the one of a
  helper lemma in the unpublished draft module `QuasiSplitSplittingReduction` of the same
  task. It is repeated here as a private theorem to avoid that import.
- In the statement of `hderiv` the argument `(S := T_K)` of `rootForm` is given explicitly.
  Without it, elaboration timed out.
- `integerValuationChamberInputs_of_isAnisotropic`: `hΨ` is
  `B.isAffineRootSystemWithRankZero_affineRoots hunit` and `hderiv` is
  `B.derivativeRoots_affineRoots_of_maximalTorus hiM`. `hT : IsSplitTorus T_K.toGrp` is the first
  component of `hiK.isSplitSubtorus`. Then `nonempty_and_isIrreducibleRoots_of_isAlmostSimple`
  with the private nonemptiness theorem gives nonemptiness and irreducibility. The `Fintype`
  instance is `(finite_simpleAffineRoots hΨ hc).fintype`. Last,
  `KPApartmentData.chamberTransitivity_of_isAnisotropic` with `hG`, `hic`, `hT` and `hC` gives
  `htrans` and `hmat`.
- `exists_transitive_titsIndexCartanExtension_of_isAnisotropic` passes these four inputs to
  `exists_transitive_titsIndexCartanExtension_of_integerValuation d B hunit hiM hc`.
- `anisotropicTitsIndexCartanExtension` and its `_spec` are `Classical.choose` and
  `Classical.choose_spec` of the previous theorem.
