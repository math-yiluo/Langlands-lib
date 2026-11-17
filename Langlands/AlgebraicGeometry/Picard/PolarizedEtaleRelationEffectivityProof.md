# Effective polarized scheme descent for a cartesian étale relation: proof

Module `Langlands.AlgebraicGeometry.Picard.PolarizedEtaleRelationEffectivityProof`.
Worker 5217, Task 7409.

`Langlands.AlgebraicGeometry.Picard.polarizedEtaleRelationEffectivity` proves exactly the
published proposition
`Langlands.AlgebraicGeometry.Picard.PolarizedEtaleRelationEffectivityStatement.{u}`, for an
arbitrary universe `u`, with no additional hypotheses. The statement and the modules it
imports are used unchanged.

## Statement

For affine `S, U`, a surjective étale `p : U ⟶ S`, an actual `E : EtaleEquivalenceRelation`
and a smooth proper `f : E.U ⟶ U`, assume `IsPullback E.t (E.s ≫ f) (f ≫ p) p`. Let
`B : EquivariantLineBundle E` have ample bundle `B.bundle.IsAmple`. Then there are
`N : Over S` and `q : E.U ⟶ N.left` with `IsPullback q f N.hom p` and
`E.t ≫ q = E.s ≫ q`.

## Proof

1. Ampleness makes the chart quasi-compact (`IsAmple.compactSpace`) and quasi-separated (the
   published `LineBundle.IsAmple.quasiSeparatedSpace`). Étaleness of `p` supplies the flatness
   and local finite presentation instances.
2. The proof applies the theorem
   `EtaleRelationQuasiAffineEffectivity.exists_effective_of_invariantQuasiAffine`
   (module `EtaleRelationQuasiAffineEffectivity`). It reduces the conclusion to the following:
   every point `x` of `E.U` lies in an open `W` with `E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W` whose open
   subscheme is quasi-affine.
3. Fix `x`. Ampleness (`IsAmple.exists_section`) gives `n ≥ 1` and a global section `σ` of
   `tensorPow B.bundle.obj n` with `x ∈ B.bundle.sectionOpen σ`.
4. Apply `EquivariantModule.exists_invariant_section` (module `EquivariantSectionDescent`) to
   the rank-one module `tensorPow B.bundle.obj n` (published `tensorPow_isLocallyFreeRankOne`)
   with the equivariant structure `B.tensorPowModule n` (module
   `EquivariantLineBundleTensorPow`). It gives a section `c` of the same power with
   `x ∈ B.bundle.sectionOpen c` and
   `E.s ⁻¹ᵁ B.bundle.sectionOpen c = E.t ⁻¹ᵁ B.bundle.sectionOpen c`.
5. `W := B.bundle.sectionOpen c` is quasi-affine by the published
   `LineBundle.IsAmple.quasiAffine_sectionOpen` (`n ≥ 1`), which finishes step 2.

The hypotheses `Smooth f` and `IsProper f` are not used. The relation-theoretic part uses the
axioms of `E` and the cartesian square. The line-bundle part uses only the actual transport
laws and ampleness of `B.bundle`.

## Helper modules

- `Langlands.AlgebraicGeometry.Picard.EtaleRelationQuasiAffineEffectivity`: invariant
  quasi-affine opens descend along `p`. This uses the published
  `UnramifiedFunctor.CompletionDescent.exists_isPullback_of_isQuasiAffine`. The descended pieces are glued by the published
  `FppfQuotientGluing.exists_quotient_of_forall_exists_quotient_restrict`. The cartesian
  square comes from Mathlib's fppf descent of isomorphisms.
- `Langlands.AlgebraicGeometry.Picard.EquivariantLineBundleTensorPow`: the transport laws
  for tensor powers.
- `Langlands.AlgebraicGeometry.Picard.EquivariantSectionDescent`: the descent coalgebra on
  `Γ(E.U, L^{⊗n})` over `Γ(S) → Γ(U)` and the resulting invariant sections.

Each helper has its own paired Markdown with the detailed argument.

## Relation to the literature

The statement is the effectivity part of Stacks Lemma 99.14.3 (Section 99.14, Tag 0D1L) for
this cartesian étale setting, as documented in the statement's Markdown. The source proof
descends the polarized algebraic space and shows it is a scheme with Lemma 74.13.1 (Tag 0D3C),
through a relative Proj of the graded algebra of sections. This proof takes another route.
Faithfully flat descent of the section modules produces invariant sections. Their generation
opens are invariant and quasi-affine and they cover the chart. These opens descend as
quasi-affine schemes and glue to `N`.
