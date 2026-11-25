# From label correctness to actual Aubert correctness of the MW recursion

Module `Langlands.Representation.Classification.MoeglinWaldspurgerAubertAssembly`,
namespace `Langlands.MoeglinWaldspurger`.

`LabelCorrectness F T` (internal) says: for every cuspidal datum `ρ` in the saturated carrier
universe `max uF uV`, real `x`, integer multisegment `a`, rank `n` and irreducible `π` of
`GL_n(F)` which is a Langlands head of `realize ρ x a`, the isomorphism class of `π` is a weak
Zelevinsky label (`Aubert.SegmentPolynomialSurjectivity.IsLabel`) of `realize ρ x (dual a)`.

`aubertCorrectness_of_labelCorrectness` derives the published `AubertCorrectness F T`.
Given heads `π` of `realize ρ x a` and `πdual` of `realize ρ x (dual a)` at a common rank `n`:

1. `realize_universeLift` identifies `(realize ρ x b).universeLift` with
   `realize ρ.universeLift x b` (the lift commutes with real twists,
   `CuspidalDatum.universeLift_twist`), so `Multisegment.isLanglandsHead_universeLift_iff`
   makes `π` and `πdual` heads of the realizations over `ρ.universeLift`.
2. Label correctness makes the class of `π` a label of `realize ρ.universeLift x (dual a)`.
3. Theorem P (`Aubert.LanglandsHeadDuality.gradedAdjustedOperator_label`) sends that label to
   the class of every Langlands head of the same multisegment, here `πdual`, in the graded
   Grothendieck group.
4. `basisClass_irreducibleIsoClass` and `gradedAdjustedOperator_homogeneous` rewrite both
   sides as homogeneous classes in rank `n`; injectivity of the direct-sum inclusion
   (`DirectSum.of_injective`) gives the equality in the rank-`n` exact Grothendieck group with
   the finite-length witnesses of the target.

`universalAubertCorrectness_of_labelCorrectness` quantifies this over all primes, fields and
topological data. No hypothesis beyond `LabelCorrectness` is used; the Library supplies
binary product exactness, the graded ring laws and a unitary additive character.
