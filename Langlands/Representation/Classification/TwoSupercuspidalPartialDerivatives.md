# Middle derivatives of supplied adjacent-product subspaces

This internal prerequisite proves
`twoSupercuspidalAdjacentProductMiddleDerivatives`, whose type is the
Prop-valued definition `TwoSupercuspidalAdjacentProductMiddleDerivatives`.
It combines existing actual Jacquet and derivative calculations; no external
result is newly asserted or translated here.

## Exact scope

Fix arbitrary prime `p`, `F : PadicField p`, supplied `T : F.TopologicalData`,
and a continuous nontrivial unitary additive character `ψ` for `T.topology`.
The field and factor-carrier universes `uF,uV` are independent. Let `k > 0`
and let `ρ,ρ'` be actual bundled supercuspidal representations of `GL_k(F)`.
Assume either `ρ' = νρ` or `ρ = νρ'` at the existing isomorphism-class level,
where `ν` is the residue-normalized real-power determinant twist of exponent
one. Let `P = ρ × ρ'` be the actual normalized product induction for the
ordered positive block shape `(k,k)`.

For every supplied invariant subspace `S` of `P` with `S ≠ ⊥` and `S ≠ ⊤`,
the actual derivative of order `k` of `SmoothRep.subrepresentation P S`,
transported from rank `(k+k)-k` to `k`, is equivalent to `ρ`. The same derivative
of `SmoothRep.quotient P S` is equivalent to `ρ'`. The conclusions are
nonempty types of actual representation equivalences, including inverse linear
maps and equivariance. The existence of `S` remains an input. The conclusion
holds in either twist orientation because the ordered Jacquet formula labels
the subspace by the original ordered pair and its quotient by the reversed
pair.

## Implemented proof

The helpers in `TwoSupercuspidalPartialDerivatives` have the following roles.

- `nonempty_firstFactor_equiv` removes a one-dimensional tensor factor with
  trivial group action. A linear equivalence with `ℂ`, tensor congruence and
  the right-unit equivalence give the carrier map; checking pure tensors proves
  equivariance.
- `finrank_rankCast` proves by equality elimination that rank transport leaves
  the actual carrier dimension unchanged. `finrank_topDerivative` writes the
  positive supercuspidal rank as a successor and applies the existing
  `SupercuspidalDerivativesProof.finrank_generalLinearDerivative_top`.
- `nonempty_twoBlockTensor_equiv` uses `Shahidi.pairSplit` and its action formula
  to identify the indexed two-factor external tensor, pulled back along the
  continuous two-block Levi equivalence, with the binary exterior tensor.
- `nonempty_partialDerivative_equiv` transports an actual equivalence between
  carriers in independent universes through the partial-localization quotient.
  It uses `Jacquet.Localization.representationEquiv`; surjectivity of the
  quotient map reduces equivariance to an original vector, where the original
  intertwining identity applies.
- `derivative_of_twoBlockJacquet` assumes an actual ordered two-block Jacquet
  equivalence for an arbitrary actual `Z` of rank `a+b`, with `a,b > 0`, first
  factor `A`, and supercuspidal second factor `B`. The universe `uZ` of `Z` is
  independent of the universe of `A,B`. Pullback along the actual continuous
  Levi-to-product equivalence and the preceding tensor identification give a
  partial-derivative equivalence. The component of
  `partialDerivativeJacquetComparison` identifies the rank-cast derivative
  of order `b` with that partial derivative. The component of
  `partialDerivativeTensor` identifies the latter with `A` tensored with the
  top derivative of `B`. Its dimension is one by `finrank_topDerivative`, so
  `nonempty_firstFactor_equiv` finishes the composition.

The final theorem applies the published
`twoSupercuspidalAdjacentProductJacquet` to the supplied proper subspace.
Its two actual Jacquet equivalences have ordered factors `(ρ,ρ')` and
`(ρ',ρ)`. Applying `derivative_of_twoBlockJacquet` twice yields precisely the
two middle-derivative equivalences. The induced representation has carrier
universe `max uF uV`, while the factors retain `uV`; composing actual
representation equivalences across universes preserves this distinction.
All rank casts and the supplied topology are retained.

## Dependency audit

At Library base `125fca1a70e8f89af98a36c8565617cd68f73be5`, recursive
inspection of the five direct project imports gives 640 existing project
modules, or 641 including this entry. External imports are Mathlib modules
and Lean's `Lean.Elab.Tactic.Omega`. The Classification portion consists only
of `ConstituentRelations`, the integral-twist-freeness statement and proof,
`Segments`, `Supercuspidal`, `SupercuspidalContragredientAux` and its statement,
`SupercuspidalDerivativeVanishing`, `SupercuspidalDerivativesProof` and its
statement, `SupercuspidalSupport`, `SupercuspidalTopDerivative`,
`SupercuspidalTwist`, `TwoSupercuspidalAdjacentJacquetProof`,
`TwoSupercuspidalAdjacentReducibilityStatement`,
`TwoSupercuspidalAdjacentStructure`, `TwoSupercuspidalProductStructureStatement`,
and this entry. The following used proof routes establish the relevant
independence; the module list alone is not the justification.

The ordered supplied-subspace Jacquet formula is the second projection of
`TwoSupercuspidalAdjacent.adjacentStructure`. Its `properStructure` proof
counts the two actual associated geometric-filtration factors, uses
nonassociated-subquotient vanishing and a minimal nonzero Jacquet module to
make this count strictly increase on invariant subspaces, and obtains length
one for the Jacquet modules of the subspace and quotient. Actual first
adjointness identifies the subspace Jacquet module with the inducing tensor.
Jacquet exactness and a two-step Jordan–Hölder matching argument identify the
quotient with the reversed tensor. The actual tensor is irreducible and
quasicuspidal by the cuspidal tensor proof. Integral twist freeness distinguishes
the two orders. `associatedJacquetFiltration` supplies its premise using the
actual geometric lemma, associated geometric pieces and deletion of zero
factors. `nonassociatedJacquetSubquotients` uses the actual geometric filtration,
proper refined induction and quasicuspidal vanishing. These arguments do not
assume a proper subspace exists. The adjacent-reducibility statement is present
in the import closure as a Prop definition; its conclusion is not supplied as
a proved input. The separate conditional full-product-structure wrapper is
not used.

The derivative comparison proofs construct equivalences of the actual quotient
presentations: localization in stages, the appropriate normalization characters,
tensor-localization comparison and top-localization iteration. The new
cross-universe helper uses only the quotient-transport construction and its
formula on representatives. No derivative Leibniz rule is used.

The supercuspidal top-dimension proof first proves top nonvanishing from proper
supercuspidal derivative vanishing and reflection of zero by the mirabolic
minus functors. The actual top quotient produces Whittaker functionals.
Whittaker multiplicity one makes every functional proportional to a fixed
nonzero one, and elementary linear duality gives dimension one. The multiplicity
one route uses generalized coefficient kernels, Shalika distribution invariance,
Gelfand–Kazhdan contragredience and Haar symmetries. The supercuspidal
contragredient auxiliary module in that route proves elementary smooth-dual
separation, admissibility/irreducibility transport and conjugation of actual
coinvariant quotients. It supplies no classification theorem. The supplied
field topology is identified with its canonical norm topology only inside the
published multiplicity-one transport, not replaced in this statement.

No used proof route invokes global support decomposition, general ordered
quotient coverage, full multisegment classification, strong-head classification,
tempered uniqueness, regular or square-integrable exhaustion, or
`SquareIntegrableLanglandsClassification`. This unit does not instantiate a
conditional support-existence or support-uniqueness theorem from
`SupercuspidalSupport`.

## Remaining host obligations

This prerequisite proves neither adjacent reducibility nor existence of a
length-two segment head. It gives no top-derivative calculation for that head,
no derivative formula for a product involving it, and no rank-three
irreducibility or composition calculation. Both repeated-cuspidal triple
transfers and their ambient extraction/refinement remain separate obligations.
