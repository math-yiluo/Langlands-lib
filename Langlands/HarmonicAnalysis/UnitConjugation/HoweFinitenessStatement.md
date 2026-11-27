# Howe's finiteness theorem on the Lie algebra of `Aˣ`

The module `Langlands.HarmonicAnalysis.UnitConjugation.HoweFinitenessStatement` states, as the
proposition `Langlands.HarmonicAnalysis.LieAlgebraHoweFinitenessStatement.{u, v}`, Howe's
finiteness theorem (Harish-Chandra's Theorem 12.1) for the Lie algebra `A` of the unit group
`Aˣ` of a finite-dimensional semisimple algebra over a nonarchimedean local field of
characteristic zero. The statement is **not** proved here.

## Statement

`LieAlgebraHoweFinitenessStatement.{u, v}` quantifies over

- a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]`: a nonarchimedean local field of characteristic
  zero;
- `A : Type v` with `[Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsModuleTopology F A]`: a finite-dimensional semisimple `F`-algebra with
  its module topology; its topological ring structure is `IsModuleTopology.isTopologicalRing`,
  bound with `haveI` inside the statement, as in `LieAlgebraFourierRegularityStatement`;
- a compact `ω ⊆ A` and an additive subgroup `L` of `A` that is open.

The claim is

`FiniteDimensional ℂ ((invariantSupportedIn ω).map (restrictToLatticeTests L))`.

Here `invariantSupportedIn ω` is Harish-Chandra's `J(ω)`: the conjugation-invariant
distributions supported in the closure of `ω^G = ⋃_u u ω u⁻¹`
(`Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution`). The linear map
`restrictToLatticeTests L` (`Langlands.HarmonicAnalysis.UnitConjugation.HoweRestriction`)
restricts a distribution to the subspace `latticeInvariantTests L` of Schwartz–Bruhat functions
on `A` (locally constant with compact support) that are invariant under translation by `L`
(`Langlands.HarmonicAnalysis.UnitConjugation.LatticeTests`). The claim says that the image `j_L J(ω)` of `J(ω)`
under this restriction `j_L` is finite-dimensional.

When `L` is a lattice (compact and open), pulling back along `A → A/L` identifies
`latticeInvariantTests L` with Harish-Chandra's `C_c(A/L)`: the quotient `A/L` is discrete, and
a function of finite support on it pulls back to a function supported on finitely many compact
cosets. Then `restrictToLatticeTests L` is his `j_L`, `T ↦ T_L`, and the claim is literally
`dim j_L J(ω) < ∞`.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15):

- Introduction, printed pp. 1–2 (PDF pp. 16–17): `Ω` a p-adic field of characteristic zero,
  `G` the group of rational points of a connected reductive group, `g` its Lie algebra with the
  adjoint action, `J`, `ω^G` and `J(ω)`. "By a lattice in `g` we mean a compact open
  `R`-submodule of `g`. If `L` is a lattice, we may regard `C_c(g/L)` as a subspace of `D`. For
  any distribution `T` on `g`, let `T_L = j_L T` denote the restriction of `T` on
  `C_c(g/L)`." Theorem 12.1 (Theorem 2 (Howe)): "Let `ω` be a compact set in `g` and `L` a
  lattice in `g`. Then `dim j_L J(ω) < ∞`."
- Part II, §12, printed p. 62 (PDF p. 77): the same theorem, proved in §§12–13.

Here `G = Aˣ`. Since `F` has characteristic zero, `A` becomes a product of full matrix algebras
over an algebraic closure of `F`, so `GL₁(A)` is a connected reductive group (a product of
general linear groups after base change); its `F`-points are `Aˣ`, its Lie algebra is `A`, and
its adjoint action is conjugation `X ↦ u X u⁻¹`.

## Open subgroups in place of lattices

Harish-Chandra states the theorem for lattices; the statement here takes any open additive
subgroup `L`, and the two forms are equivalent. A lattice is an open additive subgroup.
Conversely an open subgroup `L` contains a lattice `L'` (the lattices `ϖ^k Λ`, for a lattice `Λ`
and a uniformizer `ϖ`, form a basis of neighbourhoods of `0`). Every `L`-invariant
Schwartz–Bruhat function is `L'`-invariant, so `latticeInvariantTests L` is a subspace of
`latticeInvariantTests L'`, and `j_L T` is the restriction of `j_{L'} T` to it. Thus `j_L J(ω)`
is the image of `j_{L'} J(ω)` under a linear map, and it is finite-dimensional when
`j_{L'} J(ω)` is. For noncompact `L` the space `latticeInvariantTests L` is smaller than the
pullback of `C_c(A/L)`: for `L = A` it is zero, as a nonzero constant function on `A` does not
have compact support.

## Role in Harish-Chandra's work

Harish-Chandra uses Howe's finiteness theorem in the proof of Corollary 4.2: for a compact `ω`,
a lattice `L` and a `G`-domain `V ⊆ cl(ω^G)`, there are finitely many regular orbits `O_i` in
`V` whose restricted orbital integrals `j_L μ_{O_i}` span `j_L J(V)`. Corollary 4.2 enters his
proof of Theorem 4.4 (1) (§4, printed pp. 30–31, PDF pp. 45–46).
