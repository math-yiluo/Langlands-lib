# The noetherian/DVR reduction for reductive group monomorphisms

Worker 700.

`Langlands.GroupScheme.ReductiveMonomorphismValuativeReductionStatement.{u}` is a
statement-only proposition definition. It equates two restrictions of the published
`ReductiveMonomorphismClosedImmersionStatement`: its case over discrete valuation
rings and its case over locally noetherian schemes.

`ReductiveMonomorphismValuativeReduction.DvrCase` quantifies over a commutative
domain `R : Type u` with `IsDiscreteValuationRing R` and group schemes `G`, `H`
over `Spec R`. `LocallyNoetherianCase` instead quantifies over every
`S : Scheme.{u}` with `IsLocallyNoetherian S`. In each proposition, `G` is
reductive, `H` is separated, locally of finite presentation and quasi-compact over
the base, and every group homomorphism `f : G ⟶ H` whose underlying scheme
morphism is monic must be a closed immersion. The finite-presentation and monicity
conventions agree exactly with the original target.

This is an internal extraction of the first paragraph of Conrad's proof of
Theorem 5.3.5, p.166. After reducing to a noetherian base, that paragraph uses
properness of a monomorphism and the DVR valuative criterion, then base change
along `Spec R → S`. The forward implication stated here uses that argument
locally on the target, which also permits locally noetherian bases. The reverse
implication restricts to `Spec R`, which is locally noetherian for a DVR.

The source is Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The relevant locations are Theorem 5.3.5, p.165, its first proof paragraph,
p.166, and Definition 3.1.1, p.81, for reductivity.

The module proves neither proposition nor the equivalence. It does not state the
separate reduction from arbitrary bases to locally noetherian bases, and it does
not change or prove the original closed-immersion target.
