# Dual-choice independence of actual Harris polarized class pullback

This derived construction extends `HarrisPolarizedClassBaseChange`. It proves
that independently chosen dual-evaluation families induce equal maps on the
existing ambient polarized rational-isogeny quotient and equal natural
transformations of the original Harris level towers. It then constructs
`ambientClassTowerBaseChangeOfExists` using only existence of the constrained
actual dual inputs. The conclusion concerns ambient classes before imposing a
Lie or dimension condition.

The arithmetic inputs are the same totally real number field `E`, totally
complex quadratic extension `F`, central simple unitary datum `D` on `A`, and
signature charts `C`. The positive auxiliary left involution and Hodge form
remain those of `hodgeLevelFunctor D C`; the indices are the original
`HarrisLevel D`, with their original opposite-group transporter arrows. The
source and target are actual universe-zero schemes `S` and `T` with arbitrary
`b : T ⟶ S`, both quasi-separated. The pointed pullback uses the field-valued
point `t` of `T` and its composite `t ≫ b` on `S`. Neither algebraic closedness
nor connectedness is needed here.

All named hypotheses of the imported pullback remain explicit: pullback tensor
comparison, composition, unit coherence, associativity, left-unitor comparison
and symmetry; Picard-zero pullback, the Mumford-bundle Picard-zero property and
universal base change; integral dual-base-change naturality and full
polarization stability; the relative finite-Weil transition proposition and
rational profinite-integer/finite-adele comparison. Finite fibres at both
points, the torsion finite-etale proposition, invertibility of every indexed
torsion order, finite etale roots of unity on both bases, and ordered-pair dual
additivity for the actual positive polarized objects on both bases also remain
inputs. No flatness assumption on `b` is introduced.

For each source positive polarized action `X`, a value of
`PositivePullbackDualData ... b X` is indexed by the actual scheme
`(Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme`.
Its fields are a dual-scheme witness, dual geometry, an inverse Poincare line
bundle with its tensor evaluation isomorphism, and endomorphism additivity.
These are constrained construction data. They do not contain an independently
supplied polarized output, level orbit or class map. Two families
`dualData₁` and `dualData₂` may choose their inverse bundles and evaluations
independently. No equality of these bundles, evaluations or pulled-back
polarized representatives is asserted.

`levelDataBaseChange_related_of_dualData` proves the stronger relation-preservation
statement needed for independence. If actual source representatives `x` and `y`
are related, their pullbacks using `dualData₁ x.1` and `dualData₂ y.1` are
related in the same target setoid. The proof retains the source rational unit
and sends its actual action isomorphism, including its inverse, through
`RationalAlgebraAction.pullback b`. The integral dual-naturality theorem
`IsRationalDualPullbackMultiple.integral_baseChange_of_naturality` proves the
geometric multiplier equation at the two independently chosen target duals.
The actual Weil square `weilAdelicLevelIsogeny_baseChange`, followed by the
pullback of the original orbit equation, proves the target orbit equation.
Both imported theorems allow separate dual inputs at their two endpoints.
Thus no equality or extra compatibility of the two chosen families is required.

`ambientClassBaseChange_dualData` proves equality of functions at every
original Harris level. Quotient induction reduces the claim to one source
representative. Applying the cross-family theorem to its reflexive source
relation gives the required target relation, and `Quotient.sound` gives
equality of the resulting classes. This does not replace the setoid by a
coarser equivalence relation. Extensionality in the level and quotient class
gives `ambientClassTowerBaseChange_dualData`, equality of the entire natural
transformations. Their existing naturality includes every original level
inclusion and both Hecke transporter legs.

`ambientClassTowerBaseChangeOfExists` accepts
`dualExists : ∀ X, Nonempty (PositivePullbackDualData ... b X)`.
Classical choice selects one actual dual input for each source object, and the
existing representative pullback and quotient descent construct the natural
transformation. `ambientClassTowerBaseChangeOfExists_eq` proves that this map
is equal to the map computed using any supplied actual family, by the proved
family independence. Its component theorem
`ambientClassTowerBaseChangeOfExists_app` gives the same formula for each
quotient class. Consequently all choice made inside this constructor is
irrelevant to its value, and its naturality is inherited from the constructed
ambient tower pullback. The proposition `dualExists` remains an explicit
existence assumption; this module does not establish it.

The provenance is an internal derivation from the imported actual polarized
pullback, integral dual naturality, Weil isogeny/base-change square and the
quotient universal property. It is not a separate translation of a numbered
literature result. Original-source conventions are inherited from the imported
Harris constructions. This unit does not establish identity or composition for
successive base changes, remove the named tensor/Picard/Weil hypotheses,
compare rational-isomorphism classes with geometric-isogeny classes, construct
an unpointed moduli functor or its representing schemes, or provide coefficient
descent. Those remain separate obligations of the geometric construction.
