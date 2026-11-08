# Smooth representations of compact t.d. groups; an admissibility criterion: statements

Author: Worker 6. Module `Langlands.Representation.Compact.CompactGroupSmoothStatements`, namespace `Langlands.Renard.CompactRepresentation`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, IV.1.1, Theorem (printed p.88 / PDF p.94), and IV.1.2, Proposition (printed p.89 / PDF p.95). The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

**IV.1.1, Theorem.** Let `K` be a compact t.d. group.

- (i) Every irreducible smooth representation of `K` is finite-dimensional.
- (ii) For every finite-dimensional smooth representation `(π, V)` of `K`, there is an open compact subgroup `N`, normal in `K`, acting trivially on `V`.
- (iii) Every smooth representation of `K` is semisimple.
- (iv) Every smooth representation of `K` is unitary.

**IV.1.2, Proposition.** Let `(π, V)` be a smooth representation of a t.d. group `G`. Then `(π, V)` is admissible if and only if, for every compact open subgroup `K` of `G`, every class `σ ∈ K̂` has finite multiplicity in `Res^G_K(π, V)`. The multiplicity of `σ` is `dim Hom_K(V_σ, V)`, as defined after the IV.1.1 Corollary.

## The Lean statements

The module is a statement unit: nothing is proved. Smooth representations are the published `SmoothRep.{0, u, v} ℂ G`, over an arbitrary group carrying a topology, with carriers in an independent universe `v`.

### `CompactGroupSmoothRepresentationStatement` (IV.1.1)

It quantifies over `K : Type u` with `[Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]`, i.e. a compact t.d. group, and over a smooth representation `π : SmoothRep.{0, u, v} ℂ K`. The conclusion is the conjunction of:

1. `π.IsIrreducible → FiniteDimensional ℂ π`;
2. `FiniteDimensional ℂ π → ∃ N : OpenSubgroup K, (N : Subgroup K).Normal ∧ ∀ n ∈ N, ∀ x, π.representation n x = x`. An open subgroup of a compact group is compact, so this is (ii);
3. `IsSemisimpleModule (MonoidAlgebra ℂ K) π.representation.asModule`. The submodules of the group-algebra module are exactly the subrepresentations, which are automatically smooth, so this is semisimplicity in `M(K)`;
4. `Langlands.IsUnitarizable π.representation`: the published existence of a `K`-invariant positive definite Hermitian form on the carrier, with no norm, topology or completion. This is Renard's notion of a unitary (pre-Hilbert) representation.

### `AdmissibleFiniteMultiplicityStatement` (IV.1.2)

It quantifies over `G : Type u` with `[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]`, a t.d. group, and over a smooth `π : SmoothRep.{0, u, v} ℂ G`. The conclusion is

`π.IsAdmissible ↔ ∀ K : OpenSubgroup G, IsCompact (K : Set G) → ∀ σ : SmoothRep.{0, u, v} ℂ K, σ.IsIrreducible → FiniteDimensional ℂ (σ.representation.IntertwiningMap (SmoothRep.restrictSubgroup K π).representation)`.

That is, `dim Hom_K(σ, Res^G_K π) < ∞` for every compact open `K` and every irreducible smooth `σ` of `K`. The published `SmoothRep.IsAdmissible` asks for finite-dimensional fixed vectors under every open subgroup. For a t.d. group this agrees with Renard's condition on compact open subgroups, since every open subgroup contains a compact open one. The representations `σ` range over the universe `v`. This loses no class of `K̂`, since by IV.1.1 (i) every irreducible smooth representation of `K` is finite-dimensional, hence has an isomorphic copy in any universe.

`CompactGroupSmoothStatements` is the conjunction of the two statements.

## Remarks

- The IV.1.1 Corollary (the canonical isotypic decomposition `V = ⊕_{σ ∈ K̂} V(σ)`) and the multiplicity formula `m(σ) = dim V(σ) / dim V_σ` are not stated here.
- Renard's t.d. groups are Hausdorff, locally compact and totally disconnected topological groups. The hypotheses above state exactly this.
- The proofs (finite orbit spans via II.3.2, finite group representation theory, Haar averaging) are not formalized here.
