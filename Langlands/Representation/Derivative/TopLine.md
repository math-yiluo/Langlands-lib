# A scalar model of a nonzero irreducible top derivative

Author: Worker 357.

This is a derived supporting construction.
`Langlands.Derivative.topDerivativeLineEquiv` constructs an actual complex
linear equivalence from the full carrier of the top derivative of an
admissible irreducible smooth representation to `ℂ`, provided that derivative
is nonzero. Its parameters are every prime `p`, `F : PadicField.{uF} p`,
the supplied `T : F.TopologicalData`, every bundled nontrivial continuous
unitary additive character for `T.topology`, every natural `n`, and
`A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (n+1) F.Carrier)`.
The carrier universe `uV` is independent of `uF`.

The domain is literally
`((Derivative.generalLinearDerivative T ψ (n+1) (n+1) le_rfl).obj A)`,
with the existing determinant-normalized derivative. Nonvanishing,
irreducibility and admissibility are explicit hypotheses. The construction
chooses an equivalence; it claims no preferred basis or naturality. It
includes rank one and makes no assertion for rank zero.

## Implemented construction

The published general helper
`Classification.SupercuspidalDerivativesProof.finrank_top_of_multiplicityOne`
applies to any smooth representation with nonzero positive top derivative
and Whittaker multiplicity one. It does not require supercuspidality.
Its proof pulls the full algebraic dual back through the actual surjective
top quotient into Whittaker functionals. Multiplicity one makes all dual
functionals scalar multiples of a nonzero one. Separation of points by the
full dual then proves dimension one without a finiteness premise.

The published
`Classification.SupercuspidalDerivativesProof.multiplicityOne_of_topologicalData`
provides this multiplicity one from irreducibility and admissibility for
every supplied `T`. The private rank-cast admissibility lemma is equality
elimination. Published rank-cast preservation of irreducibility and the
definition of `generalLinearDerivative` reduce its actual top-order object
to the positive top derivative with output rank zero. The explicit nonzero
hypothesis supplies the remaining premise.

The resulting equality `Module.finrank ℂ D = 1` first supplies
`FiniteDimensional ℂ D` by `FiniteDimensional.of_finrank_eq_succ`.
`LinearEquiv.ofFinrankEq D ℂ` then returns the displayed equivalence of
entire carriers. This is actual linear data, with finite-dimensionality
proved before the finite-rank comparison.

## Provenance and scope

The only direct import is the published
`Langlands.Representation.Classification.SupercuspidalDerivativesProof`.
Its general dimension and supplied-topology helpers above have actual proved
bodies in the independently accepted and published exact-target proof module.
This construction imports those general helpers and does not invoke its
supercuspidal-only final theorem. The linear-algebra comparison is from
Mathlib. No new literature assertion is made.

## Independence audit

The transitive source audit at Library
`dac2bb9e83346876770fced17af26f0cba7f4c98` contains 304 project modules,
including this new module, and 186 external import roots. Every inherited
Lean/Markdown pair equals the current published pair. The imported
`SupercuspidalDerivativesProof` pair also matches its independently accepted
frozen bytes, and all of its 302 imported pairs are unchanged from its
reviewed base `c6045fe1328899de3416096b16eb72db93a6c7fc`.

The general dimension and multiplicity-one proof bodies were inspected.
The first uses the surjective `SupercuspidalTopDerivative.topQuotient` and
its proved Whittaker pullback, then full-dual separation. The second uses
published Whittaker multiplicity one and the equality of the supplied
topology with the canonical norm topology. This agrees with the independent
review of that published input. The only inherited derivative modules are
`Iteration`, `MirabolicMinus`, `MirabolicCharacter`, `MirabolicLatticeBox`
and `MinusVanishing`. The inherited segment and constituent-relation modules
supply definitions and transport lemmas through the general
Gelfand–Kazhdan/multiplicity-one route.

The audited closure contains none of the excluded special-head,
segment-socle, exhaustion, ordered-existence, coverage, conversion, tempered
uniqueness or square-integrable classification conclusions. It contains no
segment Jacquet or segment derivative formula, no two-supercuspidal product
module, and no segment-socle derivative proof. In particular it imports
neither the broader `TwoSupercuspidalTopDerivatives` module nor its
partial-Jacquet dependencies. Searches for the excluded names and identifiers
and for proof holes found no hits. This audit preserves the operator's
permission to use independently proved general derivative theory and the
cuspidal-only derivative route; independent acceptance alone does not waive
the exclusions.

The supporting construction leaves nonvanishing to its caller. It proves
no segment derivative formula, individual segment-head nondegeneracy,
classification theorem or product irreducibility criterion. In particular,
both directions of the host special-head irreducibility criterion remain
separate obligations.
