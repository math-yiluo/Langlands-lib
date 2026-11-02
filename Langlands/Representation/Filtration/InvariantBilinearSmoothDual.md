# Extracting actual smooth-dual quotients from invariant pairings

This derived supporting construction turns a supplied invariant bilinear form
into an actual intertwiner onto the smooth contragredient of an irreducible
admissible left input. It also applies after restriction of the form along a
supplied embedding. It does not select an irreducible subrepresentation or
prove that one exists.

For any topological group and field `k`, `rightSmoothDualMap` takes a smooth
right representation `σ` and an actual form
`B : InvariantBilinear.forms ρ σ (fun _ => 1)`. Its output is an actual
intertwiner from `σ` to `smoothContragredient ρ`. Evaluation on a vector `w`
and a vector `v` is exactly `B v w`, as proved by its application lemma.
The invariance identity gives
`B v (σ(g) w) = B (ρ(g⁻¹) v) w`, which is the full-dual intertwining identity.
The existing `smoothLift` restricts the codomain to smooth functionals: an
open subgroup fixing `w` also fixes its image. No smoothness assumption on
the left input is needed for this construction.

A nonzero form gives a nonzero intertwiner by evaluation. If the actual smooth
contragredient is irreducible, Mathlib's simple-representation alternative
makes that intertwiner surjective. This proves
`rightSmoothDualMap_surjective` over the same arbitrary field.

The two quotient constructors use complex coefficients and a supplied compact
open subgroup inside every open subgroup. All three carrier universes and
the group universe are independent. The subgroup hypothesis is explicit;
neither local compactness nor a choice of Haar measure is assumed.

`smoothDualQuotientOfNonzeroForm` assumes that `ρ` is admissible and
irreducible, `σ` is smooth, and `B` is nonzero. It returns a subtype consisting
of the actual map `σ → smoothContragredient ρ` and a proof of its surjectivity.
The map has the preceding evaluation formula. Smooth separation and admissible
bidual reflexivity, from the published general contragredient proofs, establish
irreducibility of the actual smooth dual. The private `dualIrreducible` lemma
composes those published results; it asserts no unconditional reflexivity.

`smoothDualQuotientOfLeftEmbedding` takes a supplied injective intertwiner
`i : τ → ρ`, with `τ` admissible and irreducible, a smooth `σ`, and an invariant
form on `ρ × σ` which separates the left input. Restriction along `i`
preserves left separation. Irreducibility of `τ` supplies its nontrivial
carrier, so this restricted form is nonzero. The preceding constructor
returns an actual surjective intertwiner `σ → smoothContragredient τ`.
Its value at `w`, evaluated at `x`, is exactly `B (i x) w`.

Only left separation is assumed of the ambient form; the right input can have
a nonzero kernel in the resulting quotient. It need not be admissible,
irreducible, or of finite length. There is no equivalence assertion between
the right input and the smooth dual. The result applies to supplied data on
the same group, without a highest-derivative assertion on either input.

The provenance is internal composition of the published covariant-form
restriction and nonzero lemmas, smooth-part codomain restriction, general
compact-open smooth-dual separation and bidual reflexivity, and Mathlib's
irreducible-representation map alternative. The perfect-pairing theorem in
`Smooth.Contragredient.InvariantPairingProof` instead assumes nondegeneracy
on both inputs and produces an equivalence; that stronger hypothesis is not
used here. No new literature assertion, segment formula, or classification
conclusion is introduced.

This construction addresses only the smooth-dual quotient step in the proposed
independent special-head irreducibility argument. Finite length and selection
of an irreducible derivative subrepresentation, its admissibility, the
invariant pairing on that derivative, and the remaining support arguments are
separate obligations. Neither direction of the full criterion is proved here.

The import audit at Library commit
`aa1400a0eb858f7fdc607a5bb736d8f7a705fa10` contains 39 project modules
(including this new module) and 32 external import roots. All 38 inherited
Lean/Markdown pairs match that Library byte for byte. The closure contains
no derivative or mirabolic module. Its three `Classification` modules are
`Supercuspidal`, `SupercuspidalContragredientStatement`, and
`SupercuspidalContragredientAux`. They supply the actual supercuspidal
predicate, a proposition target, and proved general duality-transfer helpers;
the proposition target is not used as a proved theorem. The quotient
construction invokes the general irreducibility-transfer helper with the
explicit separation and reflexivity proofs described above. The closure has
no excluded segment, classification, exhaustion, two-factor irreducibility,
or segment-socle derivative conclusion. This audit covers this construction;
it does not certify a future consumer's dependency closure.
