# Proof of DynamicRingUnipotentFibresStatement

Authors: Worker 125, following the proof route that Worker 3483 described in the
context of Task 5728.

`Langlands.GroupScheme.dynamicRingUnipotentFibres.{u}` has exactly the published
proposition `Langlands.GroupScheme.DynamicRingUnipotentFibresStatement.{u}` as its type.
The proposition is defined in `Langlands.GroupScheme.Dynamic.RingUnipotentFibresStatement`
([statement](RingUnipotentFibresStatement.md)), which this module imports unchanged.

```lean
theorem Langlands.GroupScheme.dynamicRingUnipotentFibres :
    DynamicRingUnipotentFibresStatement.{u}
```

For every commutative ring `R`, every group scheme `G` over `Spec R` whose structure
morphism is affine and locally of finite type, every cocharacter `χ`, every
representative `j : H ⟶ G` of `Dynamic.unipotent χ`, every field `K` and every
`y : Spec K ⟶ Spec R`, the base change `(GroupScheme.baseChange y).obj H` is unipotent.

The proof keeps the published universe `u` and adds no theorem parameter,
hypothesis or proposition-valued input. It has no helper declarations.

## Proof

After introducing all binders of the statement, the tactic proof has four steps.

1. **The base-changed group is affine.** The structure morphism of
   `(GroupScheme.baseChange y).obj G` is by definition `pullback.snd G.X.hom y`
   (`change`). `IsAffineHom` is stable under base change, so Mathlib's instances
   give `IsAffineHom (pullback.snd G.X.hom y)` (`infer_instance`).
2. **The base-changed group is locally of finite type.** In the same way,
   `LocallyOfFiniteType` is stable under base change, and `infer_instance` gives
   `LocallyOfFiniteType (pullback.snd G.X.hom y)`.
3. **The base-changed representative represents `U_{G_K}(χ_K)`.** The goal
   ```lean
   (Dynamic.unipotent (Dynamic.baseChangeCocharacter y χ)).IsRepresentedBy
     ((GroupScheme.baseChange y).map j)
   ```
   is rewritten with `Dynamic.unipotent_baseChange`, which says
   `Dynamic.unipotent (Dynamic.baseChangeCocharacter y χ) = (Dynamic.unipotent χ).baseChange y`.
   The rewritten goal is `hj.baseChange y`, an instance of
   `SubgroupFunctor.IsRepresentedBy.baseChange`: base change of a representative
   represents the base-changed subgroup functor.
4. **Field case.** The published theorem
   `dynamicUnipotentUnipotence : DynamicUnipotentUnipotenceStatement` is applied over the
   field `K` to the group `(GroupScheme.baseChange y).obj G` (with the two instances of
   steps 1–2), the cocharacter `Dynamic.baseChangeCocharacter y χ`, the group
   `(GroupScheme.baseChange y).obj H`, the homomorphism `(GroupScheme.baseChange y).map j`
   and the representation fact of step 3. Its conclusion is
   `IsUnipotent ((GroupScheme.baseChange y).obj H)`, the goal.

This is the reduction in the proof of CGP Lemma 2.1.5 ("we may assume k is a field"),
carried out through the Library's base-change compatibility of `U_G(χ)`.

## Published inputs

Library declarations used, with their modules:

- `Langlands.GroupScheme.dynamicUnipotentUnipotence` (theorem, proof of
  `DynamicUnipotentUnipotenceStatement`) in
  `Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof`.
- `Langlands.GroupScheme.Dynamic.unipotent_baseChange` (theorem) in
  `Langlands.GroupScheme.Dynamic.BaseChange`.
- `Langlands.GroupScheme.SubgroupFunctor.IsRepresentedBy.baseChange` (theorem) in
  `Langlands.GroupScheme.SubgroupBaseChange`.
- `Langlands.GroupScheme.Dynamic.baseChangeCocharacter` (definition) in
  `Langlands.GroupScheme.Dynamic.BaseChange`.

Mathlib supplies, through instance search, the base-change stability of `IsAffineHom`
and of `LocallyOfFiniteType` for `pullback.snd`.

The imports are the statement module, `Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof`
and `Langlands.GroupScheme.SubgroupBaseChange`.

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the module with
no errors or warnings. The theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`, and has the single universe parameter `u`.

## Provenance

This is an internal proof of the existing Library proposition. The route (base change of
the representative, `Dynamic.unipotent_baseChange`, then the field case) is the one
Worker 3483 recorded in the context of Task 5728 for a draft that did not carry over to
this instance; Worker 125 wrote this Lean proof and explanation. The mathematical
statement and its original-source interpretation (Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, Lemma 2.1.5; Conrad, *Reductive group schemes*, Theorem 4.1.7(4)) are those of
the unchanged published statement pair.
