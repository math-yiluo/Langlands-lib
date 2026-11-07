# Filtered colimits of ring-valued points of algebraic spaces

Author: Worker 208.

This target states the point part of Brian Conrad's claim, in *Weil and
Grothendieck approaches to adelic points* (31 December 2011), printed p.13
(start of Section 5), that Theorem 3.4 holds with finitely presented algebraic
spaces in place of finitely presented schemes. Conrad says this follows by an
étale descent argument from the scheme case and refers to the proof of
[Ols, Prop. 2.2]. He uses it on printed p.17 to identify the colimit of
`X_S(A_{F,S'})` with `X_S(A_F)`. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`; pages 13
and 17 were reread for this target.

`SpaceFilteredRingPointComparison` is a proposition; no proof is supplied
here. It quantifies over a commutative ring `R`, a small filtered category
`J`, a diagram `F : J ⥤ CommAlgCat R`, a cocone `c` of `R`-algebras with an
actual colimit witness `IsColimit c`, and an algebraic space `X` over
`Spec R`. Rings, index categories and test schemes all live in one arbitrary
universe `u`. The points are `RingPoints R X A`, the sections of `X` over the
actual spectrum `Spec A` regarded as a scheme over `Spec R`. The stage maps
are `RingPoints.changeRing`, pullback of sections along the spectrum maps of
the transition algebra maps `F.map f` and the cocone legs `c.ι.app i`.

The first clause assumes `LocallyOfFiniteTypeOverBase X`: some surjective
étale scheme atlas of `X` is locally of finite type over `Spec R`. For points
`p` at stage `i` and `q` at stage `j`, it states that `p` and `q` have equal
images over `c.pt` if and only if there are a stage `k` and arrows
`f : i ⟶ k`, `g : j ⟶ k` with equal images at `k`. This is injectivity of
the comparison map from the colimit of the stage point sets to the points
over `c.pt`, stated through its explicit equality relation.

The second clause assumes `LocallyOfFinitePresentationOverBase X`: some
surjective étale scheme atlas is locally of finite presentation over
`Spec R`. It states that every point over `c.pt` is the image of a point at
some stage. Together with the first clause (local finite presentation implies
local finite type), this says the comparison map is bijective.

Neither clause assumes that `X` is quasi-compact, quasi-separated or
separated, or that its diagonal is quasi-compact; no condition is placed on
`R` or on the algebras. The weaker locally finite type hypothesis for
equality descent, and the omission of quasi-separatedness, generalize
Conrad's finitely presented setting (he works with quasi-separated spaces
throughout Section 5). Conrad's finitely presented spaces satisfy both
hypotheses: the Library's `FinitePresentationOverRing` provides an atlas
that is locally of finite presentation. The generalization
follows the Stacks Project's limit preservation for morphisms of algebraic
spaces locally of finite presentation, which needs no quasi-separatedness.
The intended proof is the étale descent argument Conrad cites: pull back an
atlas along a point, refine to an affine étale cover, descend that cover and
the lifted atlas point to a stage with the scheme results, and glue with the
fppf sheaf property.

This target covers only the point comparison of Theorem 3.4. It does not
state descent of algebraic spaces, of their morphisms or of their properties
along the colimit, the topology on adelic points, or any arithmetic
specialization to adelic rings. Those remain separate obligations.
