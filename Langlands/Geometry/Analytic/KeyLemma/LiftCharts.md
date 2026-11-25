# Charts over which near lifts exist

`IsLiftChart g c` packages a local lifting property for the formalization of
Berkovich, *Vanishing cycles for formal schemes* (1994), §7, Key Lemma 7.2.
The strong map `g` maps the chart `c` into a target chart `w`. Finite tests
`(F, ε)` on `O(c)` determine finite tests `(G, δ)` on `O(w)`. The tests apply
on any source chart `P` of a saturated presentation, with strong maps `x`
and `y` mapping `P` into `c` and `w`, respectively. If the pullbacks along
`y` and `x ≫ g` differ on `G` by at most `δ` at every spectrum point of
`P`, some bounded `a : O(c) → O(P)` satisfies `a ∘ g* = y*` and differs
from `x*` on `F` by at most `ε`.

`RationalTestTransfer` transfers tests through rational restriction using
the defining inequalities, the bounded fractions, and polynomial
approximation. `LiftChartCover` derives test transfer for represented
affinoid domains from the rational case. It uses the finite Banach
lifting result to show that every point of an analytic domain in the
source of an étale strong map has a local cover by charts satisfying
both `IsLiftChart` and the Library's `IsRigidChart`.
