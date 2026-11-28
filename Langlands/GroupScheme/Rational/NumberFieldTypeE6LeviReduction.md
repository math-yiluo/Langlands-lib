# Totally complex type E₆ vanishing from the type A₅ Levi

`NumberFieldTotallyComplexTypeE6LeviFactorizationStatement` expresses the geometric step
in reducing a cocycle of an actual simply connected E₆ group to a Levi subgroup.
`numberFieldTotallyComplexTypeE6Vanishing_of_leviFactorization` proves that this step and
the outer type A Hasse kernel imply `NumberFieldTotallyComplexTypeE6VanishingStatement`.

## Geometric input

The base field, the numbered Tits index of the ambient group, and the cocycle have the
hypotheses of `NumberFieldTotallyComplexTypeE6VanishingStatement`. The factorization
supplies a finite Galois refinement `M/F` of `L/F`. On the refined cover a cochain twists
the pullback of the ambient cocycle to the image of a cocycle in the actual centralizer
`C` of a closed copy of `Gm`. The data retain a simply connected, absolutely almost-simple
derived subgroup `D` together with a numbering by `CartanMatrix.A 5`, and a represented
fppf quotient `C → Q` by `D`, where `Q` is a split torus. The equality of cocycles after
twisting is tested on all pairs of points of the refined cover.

The proposition records the geometric part of Platonov and Rapinchuk's reduction for
inner E₆ on printed pp. 382–383 and outer E₆ on printed p. 385. In the diagrams with
Bourbaki's vertex α₂ distinguished, the line is the connected torus cut out by the other
five simple roots. Deleting α₂ leaves the chain of type A₅. The connected central torus of
`C` is that line, so the quotient of `C` by its derived group is split. The corresponding
line in the pure inner twist can be matched by a geometric conjugation. The discrepancy
of the corrected geometric identification fixes the split line, giving the centralizer
cocycle. A finite Galois refinement accommodates the conjugating point. The proposition
packages the resulting subgroup and cocycle data without requiring a specific choice of
conjugating point or quotient presentation.

## Proof of the implication

`Cocycle.locallyTrivial_of_totallyComplex` applies
`simplyConnectedRealToAllPlacesComparison` to the identity coboundary and the given
cocycle. The real-place condition is empty. Thus the cocycle is trivial on the full
pullback of its cover at each completion. For the derived subgroup the proof tests whether
the full star action fixes every simple vertex. In the inner case it applies the number-field
inner type A kernel using `numberFieldReducedNormLocality`. In the outer case it applies
the supplied outer type A Hasse kernel. The local triviality lemma discharges localization
in both cases, so the proof can trivialize every cocycle of `D` on a finite Galois cover.

The image of the centralizer cocycle in `Q` is a coboundary by split-torus Hilbert 90. The
fppf quotient is smooth because `D` is smooth. The fibre over the trivializing cochain has
a point over a finite separable field extension, which the proof embeds in a finite Galois
extension of `F`. Twisting by this lift gives `Cocycle.kernelTwist`. The actual kernel is
isomorphic to `D` via `RelativeRoot.IsFppfQuotient.kernelIso`, so the vanishing for `D`
trivializes the kernel cocycle. Triviality passes back through the twist and refinement of
the centralizer cocycle, its inclusion into the ambient group, and the original twist and
refinement. The conclusion has the exact type of the published E₆ vanishing statement.

`TypeE6SplitLeviCocycleFactorization.isTrivial_of_derivedVanishing` applies
the quotient argument to an individual factorization and a vanishing theorem
for the particular derived subgroup.

## Source

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`, retained PDF SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`. Section 6.8,
Proposition 6.22 and the outer index list (6.53), printed pp. 378–379 (one-based PDF
pp. 388–389). The inner and outer E₆ reductions are on printed pp. 382–383 and 385
(PDF pp. 392–393 and 395). The proof here formalizes the final cohomological implication
from the geometric data and keeps the existence of those data as a hypothesis.
