# Simply connected central covers from a minimal coweight lattice

Worker 1238. This module is a derived, conditional assembly step toward
`SplitSimplyConnectedCoverExistenceStatement` (module
`Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceStatement`). It proves
that statement from three published propositions, which enter as hypotheses:

- `RootDatumExistenceStatement` (`Reductive/RootDatumStatement`; Milne Theorem
  21.11): a split maximal torus of a connected reductive group has a reduced
  root datum, indexed by a finite type;
- `CentralIsogenyRootDatumHomStatement` (`CentralIsogeny/SplitRootDatumStatement`;
  central case of Milne Proposition 23.5): a central isogeny `φ : G ⟶ G'` with
  split maximal tori `i`, `i'` and a torus map `t` satisfying
  `i ≫ φ = t ≫ i'` gives a morphism of root pairings `P' → P`. Its weight map is
  `χ ↦ t ≫ χ` and its coweight map is `ν ↦ ν ≫ t`. Both maps are injective, and
  `φ` is an isomorphism exactly when the weight map is bijective;
- `SemisimplePerfectStatement` (`Derived/SemisimplePerfectStatement`; Milne
  Corollary 21.50): a semisimple field group `G` satisfies
  `derivedSubgroup G = ⊤`.

It proves none of these three. Unlike the published assembly
`SplitCoverExistenceAssembly`, it needs neither the Existence Theorem nor the
Isogeny Theorem nor the coroot criterion for simple connectedness (Milne
23.55, 23.9, 23.29). Everything else it uses is already proved in the Library:
the lift of split maximal tori along central isogenies
(`centralIsogenySplitMaximalTorusLift`), the finiteness of the root-span
quotient of a semisimple group (`IsSemisimple.finite_quotient_rootSpan`,
`RootPairing.finite_quotient_rootSpan_iff_corootSpan`), the transpose lemma
`SplitCorootCriterion.surjective_weightMap`, and the composition theorem
`IsCentralIsogeny.comp_of_derivedSubgroup_eq_top` of
`CentralIsogeny/PerfectComposition`.

Throughout, `k : Type u` is a field, `G` a group over `Spec k`, `T` a
commutative group over `Spec k`, and `i : T ⟶ G`.

## Definitions

- `SplitCentralCoverCandidate i` is a structure with these fields: a group `C`
  over `Spec k`, a homomorphism `π : C ⟶ G` with `IsSemisimple C` and
  `IsCentralIsogeny π`, a commutative group `S` with
  `IsSplitTorus S` and a homomorphism `j : S ⟶ C` with `IsMaximalTorus j`,
  and a homomorphism `t : S ⟶ T` with `j ≫ π = t ≫ i`. So `π` is a
  semisimple central cover of `G` that carries a split maximal torus over `T`.
- `coweightImage c` is the additive subgroup `{ν ≫ c.t | ν ∈ X_*(c.S)}` of the
  cocharacter lattice `X_*(T) = cocharacterLattice T`. It is the range of
  composition with `c.t` (`Preadditive.rightComp`). `mem_coweightImage` unfolds
  this.
- `refl hG hT hi` is the candidate `(G, 𝟙 G, T, i, 𝟙 T)` for semisimple `G`
  and a split maximal torus `i`.
- `comp c f hH hf hperf j' hS' hj' t' h` is the candidate `(H, f ≫ c.π, S', j',
  t' ≫ c.t)`. Here `f : H ⟶ c.C` is a central isogeny, `H` is semisimple and
  perfect (`derivedSubgroup H = ⊤`), `j' : S' ⟶ H` is a split maximal torus and
  `j' ≫ f = t' ≫ c.j`. The composite `f ≫ c.π` is central by
  `IsCentralIsogeny.comp_of_derivedSubgroup_eq_top`.

## Statements

- `coweightImage_comp_le`: the coweight image of `comp c f …` is contained in
  that of `c`, because `ν ≫ (t' ≫ c.t) = (ν ≫ t') ≫ c.t`.
- `corootSpan_le_coweightImage hRD hHom hG hT hi hP c`: for semisimple `G`, a
  split maximal torus `i`, a root datum `P` of `i` and any candidate `c`, the
  coroot span `P.corootSpan ℤ` lies in `coweightImage c`.
- `corootSpan_index_ne_zero hG hT hi hP`: for semisimple `G`, the coroot span of
  a root datum `P` (with a finite index type) of a split maximal torus has
  nonzero index in `X_*(T)`, so the quotient is finite.
- `isSimplyConnected_of_minimal hRD hHom hPerf hG hT hi hP c hmin`: suppose that
  the relative index of the coroot span `N = P.corootSpan ℤ` in
  `coweightImage c` is at most its relative index in `coweightImage c'` for
  every candidate `c'`. Then `IsSimplyConnected c.C`.
- `splitSimplyConnectedCoverExistence_of_minimalLattice hRD hHom hPerf :
  SplitSimplyConnectedCoverExistenceStatement.{u}`. The conclusion is the
  target statement exactly. For every field `k : Type u`, every semisimple `G`
  over `Spec k` and every split maximal torus `i : T ⟶ G`, there are an actual
  group `C` over `Spec k` and an actual homomorphism `π : C ⟶ G` with
  `IsSimplyConnected C` and `IsCentralIsogeny π`.

## Proofs

**Coroots lie in every coweight image.** `RootDatumExistenceStatement` gives a
root datum `P₀` of the torus `c.j` of the candidate.
`CentralIsogenyRootDatumHomStatement`, applied to `c.π` and `c.t`, gives a
morphism of root pairings `g : P → P₀` with coweight map `ν ↦ ν ≫ c.t`. A
morphism of root pairings sends coroots to coroots
(`RootPairing.Hom.coroot_coweightMap_apply`). So `P.coroot r` is the image
`P₀.coroot (g.indexEquiv r) ≫ c.t`, which lies in the coweight image. The span
of the coroots then lies in it too (`Submodule.span_le`).

**Finite index.** `G` is semisimple, so the quotient of the character lattice
by `P.rootSpan ℤ` is finite (`IsSemisimple.finite_quotient_rootSpan`, the
"only if" half of Milne 21.48). Hence `X_*(T) ⧸ P.corootSpan ℤ` is finite too
(`finite_quotient_rootSpan_iff_corootSpan`), and the index is nonzero
(`AddSubgroup.index_ne_zero_of_finite`).

**A minimal candidate is simply connected.** Let `f : H ⟶ c.C` be a central
isogeny with `H` semisimple. We must show that `f` is an isomorphism.

1. `centralIsogenySplitMaximalTorusLift` lifts the torus `c.j` to a split maximal
   torus `j' : S' ⟶ H` with `t' : S' ⟶ c.S` and `j' ≫ f = t' ≫ c.j`.
   `SemisimplePerfectStatement` makes `H` perfect. So `c' = comp c f …` is a
   candidate.
2. Write `L = coweightImage c` and `L' = coweightImage c'`. Then `N ≤ L' ≤ L`
   (the two statements above). The tower formula
   `AddSubgroup.relIndex_mul_relIndex` gives
   `N.relIndex L' * L'.relIndex L = N.relIndex L`. The right side is nonzero,
   because it divides the index of `N` (`relIndex_dvd_index_of_le`), which is
   nonzero by the finite index statement. By minimality `N.relIndex L ≤
   N.relIndex L'`. Hence `L'.relIndex L = 1`, and `L ≤ L'`
   (`AddSubgroup.relIndex_eq_one`). So `L' = L`.
3. `RootDatumExistenceStatement` gives root data `P₁` of `j'` and `P₀` of `c.j`.
   `CentralIsogenyRootDatumHomStatement`, applied to `f` and `t'`, gives
   `g : P₀ → P₁`, with coweight map `ν ↦ ν ≫ t'` and injective weight map, such
   that `f` is an isomorphism if and only if the weight map of `g` is bijective.
   Applied to `c.π` and `c.t`, it gives `e : P → P₀` with injective coweight map
   `ν ↦ ν ≫ c.t`.
4. The coweight map of `g` is surjective. Let `μ ∈ X_*(c.S)`. Then
   `μ ≫ c.t ∈ L = L'`, so `μ ≫ c.t = ν ≫ t' ≫ c.t` for some `ν ∈ X_*(S')`. The
   map `e.coweightMap` is injective, so `μ = ν ≫ t' = g.coweightMap ν`. The
   coweight map of `g` is also injective, hence bijective.
   `SplitCorootCriterion.surjective_weightMap` then makes the weight map of `g`
   surjective. With injectivity it is bijective, so `f` is an isomorphism.

**The closing theorem.** Fix `k`, `G`, `T`, `i` as in the statement.
`RootDatumExistenceStatement` gives a root datum `P` of `i`. Every candidate has
a natural number `N.relIndex (coweightImage c)`, and `refl` is a candidate. So
`Nat.find` gives a candidate `c` whose relative index is the least value taken.
That `c` satisfies the minimality hypothesis, so `c.C` is simply connected,
and `c.π` is a central isogeny.

The closing theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The usual proof of this statement is Milne's Remark 23.60 (printed p.502, PDF
p.518): "For a split group (G,T), the universal covering is the central
isogeny corresponding to the isogeny of root data (X,Φ,Φ^∨) → (P(Φ),Φ,Φ^∨)."
That route needs the Existence and Isogeny Theorems, and the published
`SplitCoverExistenceAssembly` formalizes it. This module takes another route,
which is derived and not taken from the literature. It does not build the
cover from its root datum. It minimizes over the actual central covers of `G`
that carry a split maximal torus over `T`, measuring each cover by its
coweight lattice inside `X_*(T)`. The lattice of every cover contains the
coroot lattice, which has finite index (Milne Proposition 21.48, printed
p.439, PDF p.455), so the minimum exists. A further central isogeny onto a
minimal cover cannot shrink the lattice, so it is an isomorphism by Proposition
23.5 (printed p.485, PDF p.501). The proof does not show that the minimal
lattice is the coroot lattice, and does not need to.

Simple connectedness is the Library's `IsSimplyConnected`
(`SimplyConnected/Basic`): `C` is semisimple and every central isogeny onto
`C` from a semisimple group is an isomorphism. Its Markdown gives the sources:
the paragraph before CGP Corollary A.4.11, and Milne Proposition 19.15
(printed p.401, PDF p.417), the central-isogeny form of Milne's Definition 18.5
(printed p.388, PDF p.404) for semisimple groups. The candidate `comp` needs
the composite of two central isogenies to be central again. Milne gets this
from Proposition 18.2 (printed p.387, PDF p.403). This module gets it from
perfectness (Corollary 21.50, printed p.440, PDF p.456) through
`CentralIsogeny/PerfectComposition`.

Source: J. S. Milne, *Algebraic Groups* (2017), source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. The errata
snapshot of 2026-11-02 (`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has no
entry for Remark 23.60, Proposition 23.5, Definition 18.5, Proposition 19.15,
Proposition 21.48 or Corollary 21.50. Its Chapter 18 entries concern 18.4 and
18.8, and its p.440 entry concerns the proof of Theorem 21.51. This module uses
none of those three.
