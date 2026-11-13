# Proof: the induction sheaf has the coefficients as identity-coset stalk

Worker 141 implemented this proof for Task 5598. The entry theorem is
`Langlands.Sheaf.Renard.HomogeneousEquivalence.originStalk :
OriginStalkStatement`. It proves the published statement
`HomogeneousEquivalence.OriginStalkStatement` from
`Langlands/Sheaf/Renard/HomogeneousEquivalenceStatement.lean`, unchanged. For every
`G : Type` with a topological group structure and `SigmaCompactSpace G`, every
`hG : IsLocallyProfinite G` and every closed subgroup `H`, it gives a natural
isomorphism
`InductionSheaf.functor hG H hH ⋙ pointRestriction H hG hH ≅ 𝟭 (SmoothRep ℂ H)`.
The `SigmaCompactSpace` premise is retained in the statement but not used.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, III.3.2, printed p.85 / PDF p.91, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF p.91 was
read. The source says it is clear that the representation of `H` on the fibre of
`F_τ` over `o = H1_G` is isomorphic to `(τ, E)`, and gives no argument. The Lean
argument below is internal.

## Implemented proof

The theorem introduces the data and returns `⟨(HomogeneousOriginStalk.unitIso hG
H hH).symm⟩`. The work is in two helper modules, both submitted with this proof.

- `Langlands/Sheaf/Renard/ProjectorActionStalks.lean` covers any compatible test
  action on a locally profinite space. The germ at `x` of the original-vector
  section `(χ_W · m)_W` is a surjective complex-linear map from the original
  module onto the stalk of the reconstructed action sheaf. Its kernel is the set
  of vectors `m` with `χ_K · m = 0` for some compact open `K ∋ x`. It turns the
  module action into stalk transport and is natural for module maps.
- `Langlands/Sheaf/Renard/HomogeneousOriginStalk.lean` takes the module to be the
  published compact induction `CompactInductionTestModule.compatibleObject`. For
  a smooth `A`, evaluation `f ↦ f(1)` and the germ at `origin H` are two
  surjections from `CompactFunctions H A.representation`. They have the same
  kernel: `f(1) = 0` exactly when some compact-open test at the identity coset
  kills `f`. Surjectivity of evaluation uses the published `compactLocalSection`,
  which needs smoothness of `A`. Mathlib's first isomorphism theorem therefore
  gives a linear equivalence from `A` to the stalk, sending `f(1)` to the germ of
  `f`. Equivariance follows from covariance `f(h) = σ(h) f(1)` and the stalk
  transport lemma. Naturality follows from `compactInducedMap` and the stalk-map
  lemma. `SmoothRep.mkIso` and `NatIso.ofComponents` give `unitIso`.

Both functors are the published ones. The stalk is the literal ordinary stalk with
its published stabilizer action. No Library file is edited. A development check
reported only the standard axioms `propext`, `Classical.choice` and `Quot.sound`
for `originStalk`.

This proof is the unit half of the Task 5598 target
`HomogeneousEquivalence.Statement`. The counit half needs the separately assigned
sibling targets `EquivariantModuleStatements.SmoothStatement` (Task 5591) and
`HomogeneousSectionStatements.CompactAlphaBetaStatement` (Task 5596). It is not
part of this candidate.
