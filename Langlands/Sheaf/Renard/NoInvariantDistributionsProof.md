# Proof: Renard III.3.1 Corollary, no invariant distributions

Worker 137 wrote this proof for Task 5594. The entry theorem is
`Langlands.Sheaf.Renard.CoinvariantStatements.noInvariantDistributionsStatement`.
It proves the published closed proposition
`Langlands.Sheaf.Renard.CoinvariantStatements.NoInvariantDistributionsStatement`
from `Langlands/Sheaf/Renard/CoinvariantStatements.lean`, without changing it.
The helper declarations have the prefix
`Langlands.Sheaf.Renard.NoInvariantDistributionsProof`.

The statement covers every topological group `G : Type` with
`IsLocallyProfinite G`, every pair of locally profinite spaces `X Y : Type`
with a jointly continuous action of `G` on `X`, every `q : C(X, Y)` with
`q (g • x) = q x`, and every `F : ActionSheaf G X`. Suppose that for every
`y : Y`, every invariant `Distribution` on the actual restriction
`(InvariantFibres.restriction q hq y).obj F` to the literal fibre
`{x // q x = y}` is zero. Then every invariant `Distribution F` is zero. The
distributions are the published full algebraic duals of compact sections, and
invariance is the published `IsInvariantDistribution`. The proof adds no
premise: there is no smoothness, properness, surjectivity, countability or
nonempty-fibre assumption.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, III.3.1 Corollaire, printed p.84 / PDF p.90. The
source is registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF p.90 was read for this proof.

The printed proof goes as follows. A nonzero invariant distribution on
`F_c(X)` vanishes on `F_c(X)(G)`, so it is a nonzero linear form on the
coinvariants `F'_c(Y)`. Pick a point `y` in its support and restrict it to
the fibre `F'_y ≅ F_c(q⁻¹(y))_G`.

The Lean proof does not use that restriction step. The source map
`notes/renard/iii3-sheaf-sections.md` explains why the restriction of an
arbitrary algebraic distribution to a point stalk is not available in
general. The proof instead follows the route the task and the source map
describe, and argues by contraposition on vector spaces:

- the fibre hypothesis makes each fibre coinvariant space zero;
- the III.3.1 Proposition (`FibreCoinvariantStatement`, proved in the Library
  as `CoinvariantStatements.fibreCoinvariantStatement`) makes each stalk of
  `F'` zero;
- sheaf separation, together with the injectivity of the original
  coinvariants into the sections of `F'`, makes the global coinvariants zero;
- so every invariant distribution, which factors through the coinvariants,
  is zero.

The proof needs only the injectivity part of the compact comparison. That
part is proved directly here, so `CompactComparisonStatement` (Task 5592) is
not used.

## Implemented proof

The Lean file contains the following declarations.

- `coinvariants_subsingleton_of_forall_invariant_eq_zero`: let `ρ` be a
  complex representation of a group on `V`. If every `ρ`-invariant
  `T : Module.Dual ℂ V` is zero, then `Representation.Coinvariants ρ` is a
  subsingleton. Take `z` in the coinvariants. By
  `Module.forall_dual_apply_eq_zero_iff`, it suffices that `φ z = 0` for every
  linear form `φ`. Write `z = mk v` (`Coinvariants.mk_surjective`). Then
  `φ ∘ₗ mk` is invariant by `Coinvariants.mk_self_apply`, so by hypothesis it
  is zero, and in particular `φ (mk v) = 0`.
- `fibreCoinvariants_subsingleton`: this is the previous lemma applied at a
  point `y`, with the fibre action `InvariantFibres.fibreAction q hq y`. The
  carrier of `(InvariantFibres.coinvariants q hq y).obj F` is, by definition,
  the representation coinvariants of the compact-section representation of
  the restricted sheaf. The hypothesis of the target at `y` is exactly the
  hypothesis of the lemma for that representation.
- `module_subsingleton_of_stalks`: let `M` be a nondegenerate
  `PointwiseTestAlgebra.Carrier Y`-module. If every stalk of the published
  projector presheaf `ProjectorVectorSheaf.presheaf hY hM` is a subsingleton,
  then `M` is a subsingleton. Take `m : M`. The published original-vector
  sections `ProjectorVectorSheaf.originalSection hY hM ⊤ m` and
  `originalSection hY hM ⊤ 0` have equal germs at every point, because the
  stalks are subsingletons. So they are equal by Mathlib's
  `TopCat.Presheaf.section_ext` for the published `ProjectorVectorSheaf.sheaf`.
  By `ProjectorVectorSheaf.exists_compactOpen_action_eq`, some compact open
  `K` has `ProjectorBasisSheaf.action hY M K m = m`. The component at `K` of
  `originalSection ⊤ m` is `action K m`, by definition. Comparing the
  components at `K` gives `m = action K m = action K 0 = 0`. This is the
  injectivity of the original vector into sections, so the compact comparison
  isomorphism is not needed.
- `noInvariantDistributions_of_fibreCoinvariant`: assuming
  `CoinvariantStatements.FibreCoinvariantStatement`, the theorem proves
  `CoinvariantStatements.NoInvariantDistributionsStatement`. Fix the data and
  an invariant `T : Distribution F`.
  1. For each `y`, the fibre Proposition gives a natural isomorphism `e`. Its
     component at `F` runs from the ordinary stalk at `y` of
     `(CoinvariantSheaf.functor hX q hq hY).obj F` to
     `(InvariantFibres.coinvariants q hq y).obj F`. The latter is a
     subsingleton by `fibreCoinvariants_subsingleton`. The component is a
     mono in `ModuleCat`, hence injective (`ModuleCat.mono_iff_injective`), so
     the stalk is a subsingleton too (`Function.Injective.subsingleton`). By
     the published `CoinvariantSheaf.functor_obj`, which holds by `rfl`, that
     stalk is the stalk at `y` of
     `ProjectorVectorSheaf.presheaf hY ((CoinvariantSheaf.modules hX q hq hY).obj F).property`.
  2. `module_subsingleton_of_stalks` shows that the module
     `(CoinvariantSheaf.modules hX q hq hY).obj F` is a subsingleton. Its
     carrier is `Representation.Coinvariants (CompactSectionActions.canonicalAction hX F)`.
  3. Give the compact sections the canonical complex structure
     `NondegenerateScalars.module` that `canonicalAction` uses. The map `T` is
     then also linear for this structure, by the published
     `CompactSectionActions.canonicalScalar_eq`; call this map `T'`.
     Invariance of `T` says `T' ∘ₗ canonicalAction hX F g = T'`, because the
     operators of `canonicalAction` are the original
     `compactRepresentation F g`. So `T'` factors through the coinvariants
     by Mathlib's `Representation.Coinvariants.lift`.
  4. For each compact section `s`, `T s = lift T' (mk s)` by `lift_mk`. Here
     `mk s = 0` because the coinvariants are a subsingleton. So `T s = 0`,
     and `T = 0` by `LinearMap.ext`.
- `CoinvariantStatements.noInvariantDistributionsStatement` (entry theorem):
  this is `noInvariantDistributions_of_fibreCoinvariant` applied to the
  published theorem `CoinvariantStatements.fibreCoinvariantStatement`, which
  proves `FibreCoinvariantStatement`. That theorem is imported from
  `Langlands.Sheaf.Renard.FibreCoinvariantProof` (Task 5593). Like
  `fibreCoinvariantStatement`, the entry theorem sits in the namespace of its
  statement.

## Scope

The entry theorem proves the target with no hypothesis beyond those of the
published statement. Besides Mathlib, it relies only on published Library
results, chiefly `CoinvariantStatements.fibreCoinvariantStatement`. The
axioms it uses are `propext`, `Classical.choice` and `Quot.sound`. The Lean
file asserts no general restriction of distributions to point stalks, and it
does not use `CompactComparisonStatement`. The conditional theorem
`noInvariantDistributions_of_fibreCoinvariant` takes
`FibreCoinvariantStatement` as an explicit hypothesis. That hypothesis is a
proposition, not an axiom, and the entry theorem discharges it.
