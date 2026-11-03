# Faithfulness and coherence of actual curve-place adelic maps

`Langlands.Global.CurvePlaceAdeleArithmeticStatement` groups four structural
properties of the published actual curve-place rings and maps.

1. For fields `k` and `F` in a common arbitrary universe, an algebra structure
   `k → F`, and a nonempty type of actual discrete curve places, the diagonal
   from the outside-`S` integers to the level ring is injective for every finite
   set `S`. The set `S` itself may be empty.
2. For perfect `k` and a function field `F` with the published compatible finite
   extension presentation over `RatFunc k`, the full-field adelic diagonal is
   injective. No nonemptiness hypothesis is added here: an actual place exists
   by extension of the rational-function place at zero. Separability of the
   specified presentation and infinitude of `k` are not required.
3. Transport along the identity `k`-algebra equivalence is the identity ring
   equivalence of the actual adelic ring.
4. Transport along the composite of two `k`-algebra equivalences equals the
   composite of their adelic transports, as an equality of ring equivalences.

The last two assertions require only the field and algebra structures used by
the published presentation comparisons. They do not require perfect constants,
a rational-function presentation, or a finite extension. Thus these laws apply
to the existing restricted products whenever the actual place types and local
completions are formed, including an empty place type.

The rings are the cofinite restricted products of the actual adic completions
at `AlgebraicCurve.Place k F`, with their completed valuation subrings. The
level diagonal is the published `curvePlaceAdeleLevelDiagonal`, and the
full-field diagonal is `curvePlaceAdeleDiagonal`. The transport is the published
`curvePlaceAdeleCongr`, which already preserves the restricted-product topology.
The last two laws therefore also assert identity and composition for the
underlying functions of the existing homeomorphisms.

This is a derived structural target for the arithmetic infrastructure used in
Conrad, *Weil and Grothendieck approaches to adelic points*, December 31, 2011,
Section 2 opening, printed p.1. That passage supplies the global-field adelic
levels and their maps from outside-`S` integers; it does not state this
implementation-specific coherence package. The target is justified by
injectivity of a field into any one of its completions and by uniqueness of
continuous maps from the dense original field into each completed local field.
It is a statement to be proved, not a supplied injectivity or coherence axiom.
Identification with conventional global places, discreteness of the diagonal,
and comparisons for scheme or algebraic-space points remain separate work.
