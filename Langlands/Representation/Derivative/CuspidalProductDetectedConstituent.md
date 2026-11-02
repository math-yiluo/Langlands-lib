# A detected constituent of a fixed ordered cuspidal product

Author: Worker 357.

This is a derived supporting construction for one fixed ordered product
of actual supercuspidal representations. It combines the general
exact-functor constituent construction with independently proved
supercuspidal top nonvanishing, the scalar top-derivative constructions,
general derivative exactness, and finite length of irreducible product
induction. It introduces no additional literature assertion.

## Inputs and returned data

The parameters are every prime `p` with `Fact p.Prime`, a p-adic field
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, and a bundled
continuous nontrivial unitary additive character for `T.topology`.
The field universe `uF` and factor-carrier universe `uV` are independent.
The input is a positive total rank `n`, an ordered `B : BlockShape n`,
and actual `C i : SupercuspidalRep.{uF,uV}` of the block groups.
Each bundled factor includes its actual smooth representation,
irreducibility, and supercuspidality. Repeated factors are allowed.

Write `P` for the actual object
`(T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj)`
and `J` for `generalLinearDerivative T ψ n n le_rfl` in carrier
universe `max uF uV`. Thus `P` is the existing normalized induction
with the supplied topology, ordered upper block parabolic, positive
half-modulus normalization, and right translation.

`cuspidalProductTopDerivativeLineEquiv` returns a complex linear
equivalence from the entire carrier of `J.obj P` to `ℂ`, including an
inverse. The target group has rank zero. No basis, formula, naturality,
or canonical choice is asserted.

`CuspidalProductDetectedConstituentData T ψ B C` stores three fields:

- `topLine`, this scalar equivalence for the whole top derivative;
- `finite_length`, finite length of the actual group-algebra module of `P`;
- `detected : ExactFunctorDetectedConstituent.Data J P`.

The last field contains an actual smooth representation `D` in the product
carrier universe, a proof of its irreducibility, an actual
`SmoothRep.IsSubquotient D P` occurrence, and nontriviality of `J.obj D`.
For every actual irreducible subquotient `E` of this same `P` with
nontrivial `J.obj E`, it also returns an actual equivariant linear
equivalence `D.representation.Equiv E.representation`. This is uniqueness
of the detected irreducible class as actual equivalence data. It is not a
choice of a literal subrepresentation or a claim that the occurrence has
multiplicity one.

`chooseCuspidalProductDetectedConstituent` constructs all these fields from
the displayed inputs alone. It has no additional finite-length,
exactness, nonvanishing, scalar-equivalence, or segment hypothesis.
Total rank zero is outside the constructor.

## Implemented construction

The private `positiveCuspidalTopLine` reduces a positive block rank to
successor rank. The published supercuspidal top-derivative theorem
`Classification.SupercuspidalTopDerivative.nontrivial_generalLinearDerivative_top`
gives nontriviality, with nontriviality of the original carrier obtained
from irreducibility. Supercuspidality supplies admissibility.
`topDerivativeLineEquiv` then gives the scalar equivalence. This last
construction uses proved Whittaker multiplicity one and separation by
the full dual; no finite-dimensionality premise is supplied here.

The finite-product scalar constructor accepts factors in carrier
universe `max uF uV`. The present input factors retain their original
universe `uV`. To bridge this difference, define
`σ i := SmoothRep.universeLift.{uF} (C i).obj`.
The published lift equivalence transfers irreducibility and
supercuspidality to each `σ i`. The preceding positive-rank argument
gives its entire top derivative a scalar equivalence. Apply
`finiteProductTopDerivativeLineEquiv` to these lifted factors.
That published construction uses the general Leibniz top comparison,
ordered head/tail induction and singleton comparison.

Let `Q` be the normalized induction of `σ`. The actual blockwise lift
equivalences induce `E : P ≅ Q` through
`T.normalizedProductInducedEquiv B`. Both induced carriers already have
universe `max uF uV`: the original factors need no universe inequality.
Map `E` through the same functor
`generalLinearDerivative.{uF,max uF uV} T ψ n n le_rfl`.
Compose its underlying linear equivalence with the scalar equivalence for
`Q`. This proves `cuspidalProductTopDerivativeLineEquiv` on the original
product `P`. No comparison between derivative functors at different
carrier universes is asserted or needed.

For the final constructor,
`Classification.irreducibleProductFiniteLength F T` gives finite length
of `P` from the irreducibility of its original factors.
`generalLinearDerivativeExactness F T` gives
`Mirabolic.MapsShortExactIntertwiners J`.
The private `preservesZero_of_exact` derives preservation of zero
morphisms from this short-exactness hypothesis. Indeed,
`ExactFunctorIrreducibility.obj_subsingleton` shows that the image of
the bottom subrepresentation of any source object is a zero carrier.
Factor a zero map through that subrepresentation. Functoriality and the
zero image force the mapped composite to be zero.

The scalar equivalence gives `Module.finrank ℂ (J.obj P) = 1`.
`ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one` proves
irreducibility of the whole image. Apply
`ExactFunctorDetectedConstituent.choose J hJ P hP hirr`, using the locally
derived zero-map instance. That generic construction chooses a source
composition factor whose image is nonzero; exact transport to the
irreducible image forces every detected factor to come from the same
grade. It supplies precisely the actual occurrence and equivalences
stored here. All choices are noncomputable.

## Provenance and dependency boundary

The six direct imports are `Filtration.ExactFunctorDetectedConstituent`,
`Filtration.ExactFunctorIrreducibility`, `Derivative.FiniteTopLine`,
`Derivative.TopLine`, `Classification.IrreducibleProductFiniteLengthProof`,
and `Induction.BlockEquivalence`.
The construction is internal composition of these actual APIs; its
mathematical content is the displayed application and universe transport.

At submission the generic `ExactFunctorDetectedConstituent` pair has
independent semantic approval and successful machine validation but
awaits publication. Its frozen pair is the sole unpublished inherited
pair in this import closure. It is a separately submitted generic
prerequisite, not an additional integration payload of this unit.
It must be published before this unit can be integrated or used as a
proved Library input. All other inherited pairs match published Library
`b1c8a5e809be36100da09da81385a7ca6789ae80`.
This submission supplies no publication or host-completion evidence.

## Independence audit

The native recursive inventory records 807 project modules including
this module and 251 external import roots. There are no missing modules
or missing Markdown pairs. All 805 inherited pairs other than the
separately reviewed generic prerequisite match the named Library
byte for byte; that prerequisite matches its frozen reviewed pair.
The remaining new pair is this module.

The closure combines the earlier audited generic constituent,
finite-product top-line, supercuspidal top-line and product-finite-length
closures. The eleven inherited additions beyond those inventories are
`ExactFunctorIrreducibility`, `ExactSmoothSubquotients`,
`SubquotientAlgebraProof`, `SubquotientAlgebraStatement`,
`Smooth.ConstituentSupport`, `Smooth.FiniteLengthGrothendieck`,
`Smooth.IrreducibleCompositionFactors`,
`Smooth.IrreducibleGrothendieckProof`,
`Smooth.IrreducibleGrothendieckStatement`,
`Smooth.IrreducibleRealization`, and `VirtualRepresentation.Integral`.
These provide generic exact-subquotient, finite-length, Grothendieck and
support algebra. The invoked exact-functor helpers have proved bodies
with their functor hypotheses explicit. The new algebra branch supplies
no classification or derivative nonvanishing assertion.

The lower derivative inputs are the independently proved and published
general derivative exactness and Leibniz rule, and the independently
proved cuspidal-only top nonvanishing and multiplicity-one route.
The finite-length branch uses cuspidal embedding, cuspidal induction
length, and actual ordered regrouping. Its earlier body and import
audits remain applicable: the inventoried inherited Lean hashes are
unchanged. The only differences from the earlier private inventories
are the now-published `TopLine` and `FiniteTopLine` Markdown, both
matching the current Library. This is a combined import, byte and
targeted proof-body audit, not a claim to have reread every inherited
module.

The code closure contains none of the excluded special-head,
segment-socle, parent uniqueness, exhaustion, ordered-existence,
quotient-coverage, ordered-conversion, tempered-uniqueness or
square-integrable classification conclusions. Searches cover their
Lean names, lower-case proof names and supplied task identifiers.
It imports no segment Jacquet formula, Zelevinsky 1980 segment derivative
formula, partial-Jacquet two-supercuspidal product argument, or
segment-socle derivative proof. The generic zero-map and
one-dimensional-image arguments do not use the stronger
nonvanishing-on-all-subquotients irreducibility criterion. Proof-hole
and forbidden-execution-command scans found no hits.

This single-product construction proves neither irreducibility of `P`
nor nonvanishing of every constituent. It makes no assertion comparing
different ordered products and gives no derivative formula or
nonvanishing result for an individual special head. Those steps, the
linked-pair converse, and both directions of the full repeated-segment
`SegmentHeadProductIrreducibility` criterion remain open.
