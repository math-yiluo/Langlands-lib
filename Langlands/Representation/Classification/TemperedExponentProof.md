# The analytic tempered exponent criterion for `GL_n`

Worker 349 assembles this proof. Its necessity helpers adapt published proof
code by Workers 819 and 219 from
`ProductLeviTemperedExponentNecessityProof` and by Worker 851 from
`TemperedOppositeJacquetScalarLayerAssembly`; these workers are coauthors.
The other inputs are imported published theorems.

`Langlands.glTemperedExponentCriterion` proves exactly
`Langlands.GLTemperedExponentCriterionStatement.{uF,uV}` from
`Langlands.Representation.Classification.TemperedExponentStatement`.
For a positive rank and an admissible complex representation of `GL_n(F)`
with the supplied scalar action through `ω`, analytic temperedness is equivalent
to the bound `‖χ(a)‖ ≤ 1` for every actual normalized upper Jacquet exponent
and every tuple whose normalized absolute values are monotone.
The field and carrier universes are independent. The carrier may be zero.
The hypotheses on admissibility and the scalar action are exactly those of
the statement.

This is an internally derived assembly of the published analytic and algebraic
results named below. The original-literature background and normalization
conventions remain those documented in the statement's unchanged Markdown.
The implemented proof uses the product-Levi theorems rather than constructing
a new Harish-Chandra `Ξ` estimate.

## Analytic temperedness implies the exponent bounds

The private `upperExponentHypothesis_of_tempered` assembles
`ProductLeviNecessity.norm_le_one_of_diagonal` and
`ProductLeviNecessity.norm_le_one_of_mem_center` using
`ProductLeviNecessity.norm_le_one_of_test`. The test-scalar lemmas verify their
weak contraction, diagonal-block and modulus conditions. This proves the
refined upper exponent hypothesis for any product-Levi representation
tempered modulo its full center for the supplied Borel Haar measure.
These published helpers have no irreducibility hypothesis. The assembly
adapts the proof of the published necessity theorem, omitting its unused
irreducibility premise.

For a nontrivial carrier, the private `jacquet_bound_of_tempered` applies that
result to the one-block shape
`C := CuspidalSupport.LeviAdmissibility.oneBlock n hn`.
The continuous group equivalence `ScalarLayer.oneBlockLeviEquiv T hn`
evaluates the unique block. Pulling `π` back along this equivalence gives `σ`.
A Borel Haar measure on the actual `GL_n` quotient exists by
`T.exists_isHaarMeasure_centralQuotient`. Its image under
`centralQuotientCongr` is a Haar measure on the one-block quotient, and
`isTemperedModCenter_comp_continuousMulEquiv` transports analytic
temperedness to `σ`.

The resulting unitary full-center character supplies
`ScalarLayer.blockScalarCharacter`. Its norm is one, and its kernel is open
by smoothness and continuity of the block-scalar map.
`ProductLeviTemperedFactorization.jacquetExponent_bound_of_core` then
transfers the refined upper bound to every ordinary normalized upper Jacquet
exponent of `π`. Its inclusion and contraction maps are the identity on the
carrier. The unique outer block contains the given shape `B`; the conditions
on other outer blocks are vacuous. This adapts the published one-block
factorization proof without using irreducibility.

## The exponent bounds imply analytic temperedness

For a nontrivial carrier, `glTemperedExponentEdge.2` constructs an actual
`UnitaryCentralCharacter π` from admissibility's smoothness component, the
scalar action through `ω`, and the weak exponent bounds. This construction
uses the one-block exponent to force `‖ω(a)‖ = 1`, so unitarity of `ω` is
not an additional assumption.

The published `glOneBlockUpperExponent` transfers the ordinary bounds to
`ProductLeviChamber.UpperExponentHypothesis T C σ`. Its algebraic comparison
uses the actual normalized refined and ordinary Jacquet modules, flattened
scalar coordinates, generalized eigencharacters and weak chambers.
No comparison hypothesis is introduced here.

Admissibility and the unitary central-character datum transport to `σ` along
the same continuous group equivalence.
`ScalarLayer.tempered_of_upperExponentHypothesis` then gives analytic
temperedness of `σ` for the image of each supplied Borel Haar measure on
`GL_n(F)` modulo its full center. This published sufficiency theorem applies
to arbitrary admissible carriers with the supplied unitary datum.
`isTemperedModCenter_comp_continuousMulEquiv`, applied to the inverse
equivalence, transports the result back to `π`. The final representation
identity is proved by evaluating the inverse equivalence.

Both transports use the actual quotient by the full group center and its
Haar measures. The analytic conclusion is the original `T.IsTempered`:
every descended smooth-dual coefficient norm belongs to `L^(2+ε)` for each
real `ε > 0` and every Borel Haar measure. It is not defined by an exponent
condition.

## Zero carrier and scope

The final theorem first splits the carrier into the subsingleton and
nontrivial cases. In the subsingleton case, `glTemperedExponentEdge.1`
supplies analytic temperedness and the absence of Jacquet exponents, proving
both directions. The nontrivial case uses the two arguments above.

The weak chamber includes walls and central directions throughout. The proof
requires neither irreducibility nor finite length and has no supplied
analytic bridge. All auxiliary comparison and analytic inputs are published
theorems. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.
