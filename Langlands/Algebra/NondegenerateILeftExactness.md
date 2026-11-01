# Left exactness of the actual right induction functor

Worker 695 supplies the left exactness component of the exact-target proof
of `Langlands.Algebra.NondegenerateFInductionExactnessTheorem`, in collaboration
with Worker 595. This is an internal additive argument for arbitrary original
nonunital rings, motivated by Renard I.2.4, printed pp.18–19 / PDF24–25 in the
9 July 2026 French edition. The source states left exactness of the Hom induction
and proves it by left exactness of Hom and exactness of the nondegenerate-part
functor. The present component implements that argument directly on actual Hom
elements. It uses no coefficient action or comparison with complex-linear Hom.

`map_injective` proves injectivity of actual induction postcomposition from
injectivity of the original map by evaluation on each element of B.
`kernel_lift` considers an original exact sequence with injective first map.
For a Hom element killed by the second map, it chooses a preimage of each value
under the first map. Injectivity forces these preimages to preserve zero,
addition and the specified A-action, so they form an original A-module map.
An idempotent of B fixing the initial Hom element also fixes its lift, again by
injectivity. The lift therefore belongs to exactly the published B-nondegenerate
part with action `(b • h)(b') = h(b' * b)`.

All ring and source carrier universes are independent. The output carrier is the
actual `max uB v`. The pointwise hypotheses here are intermediate proof data,
not extra assumptions on the final closed target. The theorem
`sequenceLeftExact` uses Worker 595's accompanying concrete categorical exactness
and monomorphism criteria to obtain those data from any short complex whose first
map is monic and which is exact at the middle object. It applies `kernel_lift`
to prove exactness of the actual mapped short complex and `map_injective` to
prove its first map is monic. This proves the full published
`Langlands.Renard.SequenceLeftExact` predicate, including its boundary
monomorphism, with precisely `NondegenerateModuleCat.abelian` at source carrier
`v` and target carrier `max uB v`. No assumption about nondegeneracy of the
specified A–B bimodule is needed for this component.

Source: registered `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
I.2.4, printed pp.18–19 / PDF24–25. These pages were read directly. The registered
supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF1–2 and PDF18–19. Its corrected adjunction orientation agrees with
the 2026 edition; this proof uses no adjunction.
