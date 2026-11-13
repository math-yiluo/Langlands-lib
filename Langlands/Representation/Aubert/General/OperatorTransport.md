# Aubert's unadjusted operator across an equivalence of ambient groups

This internal module extends the published functor transport of
`Langlands.Aubert.General.GroupTransport` (module `GroupTransport`) from single
parabolic terms to the whole unadjusted alternating operator. It is a helper
for the Family 5 comparison proof
(`GeneralLinearRationalComparisonProof`). It states no assertion of Aubert's
paper beyond the definition of the operator, Aubert 1995
(`aubert-1995-duality`), Définition 1.5, printed p. 2181. Its content is derived:
pulling representations back along an isomorphism of ambient groups commutes
with every construction used in the definition.

All declarations live in namespace `Langlands.Aubert.General.GroupTransport`.
The ambient groups `G` and `H` lie in one universe `uG`. A continuous
multiplicative equivalence `e : H ≃ₜ* G` is fixed. Subgroup compatibility always
means the literal membership equivalences `x ∈ P' ↔ e x ∈ P` (and similarly for
`M`, `U`), as in `GroupTransport`.

## Declarations

- `pullbackPullbackSymmIso e A` is the isomorphism
  `pullback e (pullback e.symm A) ≅ A` of smooth complex representations of
  `H`. It is the identity on the carrier; equivariance is
  `e.symm (e g) = g`.
- `continuous_projection_transport` says: if the Levi projection
  `P → M` of a semidirect decomposition `P = M ⋉ U` in `G` is continuous, so is
  the Levi projection `P' → M'` of a corresponding decomposition in `H`. Proof:
  by the published `projection_transport`, the second projection equals
  `(subgroupEquiv e hMM').symm ∘ h.projection ∘ subgroupEquiv e hPP'`, a
  composition of continuous maps.
- `inductionPreservesFiniteLength_transport` says: if normalized induction
  from `M` to `G` preserves finite length, so does normalized induction from
  `M'` to `H`. Here `G`, `H` are locally compact nonarchimedean and both
  unipotent subgroups are closed. Proof: for a finite-length `A` over `M'`,
  pull it back along the inverse of the restricted equivalence to get `A₀` over
  `M`. Induce `A₀` to `G`, which has finite length by hypothesis. Pull the
  result back along `e`; by `pullbackFunctor_preservesFiniteLength` it still
  has finite length. The published `inductionIsoApp` identifies it with the
  induction of `pullback (A₀)` to `H`. The functor applied to
  `pullbackPullbackSymmIso` identifies that with the induction of `A`. Finite
  length passes along both isomorphisms by `hasFiniteLength_of_iso`.
- `jacquetPreservesFiniteLength_transport` is the analogous statement for the
  normalized Jacquet functor from `G` to `M`, with the same proof, using
  `jacquetIsoApp`. It needs only the `M` and `U` compatibilities.
- `alternatingOperator_transport` is the main result. Take two finite index
  types `ι`, `κ` (independent universes `uI`, `uJ`), subgroup families
  `P M U : Finset ι → Subgroup G` and `P' M' U' : Finset κ → Subgroup H` with
  semidirect decompositions, closed unipotent subgroups and
  `ParabolicFiniteLength` data at carrier universe `max uG uV`. Take an
  index equivalence `σ : κ ≃ ι` such that, for each `J : Finset κ`, the
  subgroups `P' J`, `M' J`, `U' J` correspond under `e` to the subgroups at
  `σ.finsetCongr J`. Then on exact finite-length Grothendieck groups

  `pullback e ∘ alternatingOperator P M U … = alternatingOperator P' M' U' … ∘ pullback e`.

  Proof: by `LinearMap.ext` and `alternatingOperator_apply`, both sides are sums
  over finite index sets. The left sum is reindexed along `σ.finsetCongr`
  (`Fintype.sum_equiv`). The signs agree because `σ.finsetCongr` preserves
  cardinality (`Finset.card_map`). The terms agree by the published
  `inductionJacquetK0_transport`, applied at each `J`.

The finite-length transports let a caller derive the finite-length premises
of one family from those of the other.
