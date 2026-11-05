# Proof of open-immersion descent over the original ring system

`Langlands.AlgebraicGeometry.SchemeLimitModel.ringSystemOpenImmersionDescent`
proves exactly the published proposition
`Langlands.AlgebraicGeometry.SchemeLimitModel.RingSystemOpenImmersionDescent`
in arbitrary universe u. It conjoins the actual algebra-colimit spectrum form,
the original ring-system form above any chosen initial stage, and the original
finite-presentation form.

The source clause is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp. 5–6, Theorem 3.4(2), open immersion,
with the finite-presentation convention immediately preceding the theorem.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The spectrum and initial-ring forms with weaker model hypotheses, and the
extension from directed posets to arbitrary small filtered categories, are
derived formulations described in the unchanged statement Markdown.

The Lean proof reuses Worker 105's completed shared proof without changes.
Worker 148 checked the specialization against the published target and
prerequisite proofs and expanded this explanation. The proof imports its
published dependencies by Lean name; the submitted pair adds only this
original-ring specialization.

`spectrumOpenImmersionDescent` starts with an actual filtered diagram F of
commutative R-algebras, its cocone c and an `IsColimit c` witness. Its models
X and Y lie over Spec R and f is their actual morphism over that base. It
assumes local finite presentation and quasi-compactness of X.hom, and local
finite presentation and quasi-separatedness of Y.hom. The conclusion is an
if-and-only-if between open immersion of the actual `baseChangeMap` along
`spectrumBaseMap R F c` and open immersion of the corresponding map along
`(spectrumStructure R F).app (op j)` for some original stage algebra j.

For the forward implication, the proof applies the exported helper
`AffineLimit.exists_isOpenImmersion_baseChangeMap` to `spectrumDiagram`,
`spectrumStructure`, `spectrumCone`, the constructed `spectrumConeIsLimit`
witness and `spectrumCone_compat`. Its compact-image, inverse-factorization
and two-identity descent argument is implemented in the imported
`SchemeLimitOpenImmersionProof` and explained in its paired Markdown. The
helper retains precisely the four model hypotheses above, without source
quasi-separatedness or target quasi-compactness. Taking the unop of the
cofiltered stage index gives the required stage of F. Conversely,
`AffineLimit.cone_baseChangeMap_isPullback` identifies the limiting morphism
as the actual base change of the chosen stage morphism. Flipping that square
supplies the orientation for `MorphismProperty.of_isPullback`, so stability
of scheme open immersions under base change proves the reverse implication.

`initialRingOpenImmersionDescent` starts with the original filtered ring
functor F, its original colimit cocone c and a chosen stage j₀. With the same
four model hypotheses, it specializes the spectrum theorem to
`initialRingAlgebraDiagram F j₀` and `initialRingAlgebraCocone F j₀ c`.
`initialRingAlgebraCoconeIsColimit F j₀ c hc` constructs its algebra-colimit
witness from the original ring-colimit witness. Definitional reduction gives
exactly `Spec.map (c.ι.app j₀)` at the colimit and exactly
`Spec.map (F.map j.hom)` at the eventual stage `j : Under j₀`. Thus j carries
an actual arrow from the chosen original stage, and the construction keeps
the original rings, colimit ring and transition maps. For a directed poset,
this is a stage greater than or equal to j₀.

`finitePresentationInitialRingOpenImmersionDescent` retains local finite
presentation, quasi-compactness and quasi-separatedness of both model
structure maps and applies the preceding theorem. These are all six
finiteness hypotheses of the source form, including over nonnoetherian
rings. The final theorem conjoins the three results. The models may be
nonaffine and nonseparated, and the ring transitions may be noninjective.
There is no additional finiteness premise on the relative morphism f.
The other property clauses and whole-paper completion remain with the
parent task.
