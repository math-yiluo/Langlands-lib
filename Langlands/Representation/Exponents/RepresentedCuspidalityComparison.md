# Comparing represented and standard cuspidality

This internal supporting construction for the represented cuspidal/remainder
splitting implements the comparison behind Renard VI.2.1 Remark 1 (printed
p.137 / PDF p.143), used in VI.3.5 (printed pp.146–147 / PDF pp.152–153).
The source is the French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The explicit standardization object and its implementation are derived
adapters for the Library's actual group-scheme interfaces, rather than
separate named results of the source.

`ProperParabolicUnipotentStandardization` records a proper finite standard
face, a rational conjugating point, and the exact conjugation identity for
the point image of the originally supplied geometric radical.
`properParabolicUnipotentStandardization` constructs this data for every
proper actual parabolic and supplied rational Levi and geometric radical.
It retains `ParabolicDynamicStatement`,
`SmoothMaximalSplitTorusConjugacyStatement`, the connected reductive ambient
group, the chosen maximal split torus, a generic cocharacter, the actual
relative-root-system realization and finiteness of the actual simple roots.
These structural inputs are not proved in this module.

The published simultaneous standard-conjugation construction supplies a
rational point and a standard face. The finite set of actual simple roots
representing that face is proper: for the full set the standard cocharacter
can be zero, so the parabolic functor would be the whole group. Uniqueness
of the represented subgroup would make the original proper parabolic
inclusion an isomorphism, a contradiction. The published reductive
contraction theorem identifies the original supplied geometric radical with
the dynamic unipotent radical after conjugation. The all-test subgroup
identity then gives the stated exact identity on rational point subgroups.
Classical choice packages the resulting witnesses in the standardization
object.

`isSupercuspidal_of_isCuspidal` applies this construction to every proper
actual parabolic tested by the published represented `IsSupercuspidal`
predicate. Translation by the representation of the conjugating point gives
the published linear equivalence between the original and standard
coinvariants. Its injectivity transfers subsingletonness from the standard
Jacquet carrier to the represented normalized Jacquet carrier. Normalization
changes the action, so no normalization-character comparison is needed for
this vanishing conclusion. The standard semidirect-decomposition and
closed-unipotent witnesses are explicit inputs.

`isSupercuspidal_iff_isCuspidal` combines that reverse implication with the
published `isCuspidal_of_all_represented_parabolics`. This equivalence also
retains `StandardCocharacterStatement` for the forward implication and uses
its canonical standard semidirect-decomposition witness. The field and
representation-carrier universes are independent. Every supplied actual
Levi and matching geometric radical is tested, with no irreducibility,
admissibility, dimension or length restriction. These comparisons do not
assert compact-restriction finiteness or the existence of a cuspidal/remainder
splitting.
