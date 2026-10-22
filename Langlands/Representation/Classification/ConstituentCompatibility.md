# Constituent compatibility statements

Worker 47 authored this proposition family as a prerequisite to the segment,
special-quotient and multisegment statements. These are statements, with no
proofs or existence assumptions for classification quotients.

`AllPadicGLConstituentCompatibility` quantifies over every prime, every actual
`PadicField p`, and every positive rank. The group is Mathlib's invertible
`Fin n` matrices over that field. Complex representation carriers range over
an arbitrary fixed universe and are not required to be finite dimensional.
The algebraic part has no topology restriction. For contragredience, the
field has its existing canonical spectral topology and the general linear
group has the matrix-unit topology. No absolute-value character is used
here, so this topology choice does not confuse the spectral norm with the
residue-normalized norm required in segment induction.

The family has the following content.

| Declaration | Exact content |
| --- | --- |
| `TwistConstituentCompatibilityFor` | Common twisting by an actual unit-valued homomorphism preserves and reflects the four quotient/subrepresentation/head/socle relations. This algebraic statement allows all such characters; no unitary restriction is imposed. |
| `ConstituentIsomorphismUniquenessFor` | Two actual irreducible heads, or two actual irreducible socles, of the same representation are isomorphic by an equivariant linear equivalence. |
| `HasGLCentralCharacter` | The character is evaluated on actual scalar matrices. It is a predicate, not an assumed chosen central-character function. |
| `GLConstituentCentralCharacterFor` | A prescribed central character passes to an irreducible quotient or subrepresentation. Twisting by `χ ∘ det` changes `ω` to `ω χ^n`, including the rank factor. |
| `AllPadicGLAlgebraicConstituentCompatibility` | The preceding statements on the actual all-fields, all-positive-ranks general linear groups. |
| `AllPadicGLContragredientConstituentCompatibility` | For smooth admissible source and target, the smooth contragredient exchanges irreducible head and socle relations. It changes a prescribed central character to its inverse. |
| `AllPadicGLConstituentCompatibility` | Conjunction of the concrete algebraic and contragredient families. |

All head/socle uniqueness quantifiers are over the same carrier universe.
The dual carrier is the smooth-vector submodule of the full algebraic dual.
Admissibility and smoothness are explicit hypotheses of the dual assertions.
There is no finite-dimensional algebraic-dual replacement.

For arbitrary continuous quasicharacters of `Fˣ`, algebraic twisting is already
covered by the homomorphism statements. Applying these statements inside the
smooth category also requires the existing locally constant/open-kernel twist
results. This file does not assert that an arbitrary character on an arbitrary
topological group preserves smoothness.

## Original sources and derivation boundaries

Bernstein–Zelevinsky 1977 §1.2–§1.5, p.443 (PDF p.4), defines smooth modules,
subquotients, the smooth contragredient, and scalar twists, including the
inverse-character rule. Its §2.3(d), p.446 (PDF p.7), states compatibility
of normalized induction with contragredience. Zelevinsky 1980 §3.1–§3.3,
pp.180–181 (PDF pp.17–18), distinguishes the segment submodule and quotient
orientations and reverses/dualizes the endpoints under contragredience;
§9.1 and §9.4, pp.197–198 (PDF pp.34–35), concern the special quotient.
Those original passages were read directly.

The present generic constituent assertions are elementary structural
prerequisites of those source formulas, stated explicitly as derived/internal
targets. Their whole arbitrary-group algebraic scope is not quoted as a
theorem from the originals. Equality of kernels/images under a common twist
and the first isomorphism theorem explain the algebraic clauses; exact smooth
duality and admissible biduality are proof prerequisites for the dual clauses.
These explanations are not proofs.

The central-character twist formula follows from
`det(a I_n) = a^n` and the definition of the action. Passing a scalar action
through an actual surjection or injection gives the other central-character
clauses. No independent analytic assertion is hidden in these predicates.

Henniart 2002 §2.6, p.595 (PDF p.9), must eventually use the corrected special
formula
`δ_m(ρ)∨ ≅ ν^(1-m) δ_m(ρ∨)`.
Its displayed formula omits the dual on `ρ`; the missing dual is visible in
the original and is corrected by Zelevinsky §3.3 and §9.4. This constituent
prerequisite does not by itself establish that formula: normalized induction,
the norm character, and the existence/uniqueness of the special quotient
remain separate inputs.

Registered original fingerprints:

- `bernstein-zelevinsky-1977-induced-i`:
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- `zelevinsky-1980-induced-ii`:
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- `henniart-2002-characterization`:
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

## Dependency and acceptance boundary

The direct project imports are the companion `ConstituentRelations`,
the existing scalar twist definition, the existing smooth contragredient
definition, and the existing `PadicField` definition. The following exact
versions were checked against the current Library at commit
`1804f2a6d98d21c2bbfa3c73ccf807df74c484bb` and the local source hashes.
All seven dependency modules have the same Lean bytes as in the successful
development check below. Their transitive definition imports are also listed.
Module names are the import interface; the archived submission identifiers
below retain the original publication provenance.

| Imported module suffix | Artifact and version |
| --- | --- |
| `LocalField.Definitions` | `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, v1 |
| `Representation.Twist.Definitions` | `c83db975-8b79-4fbb-9901-2db836910a0a`, v1 |
| `Representation.Dual.Definitions` | `079d7c1a-8b96-4917-997a-536d6954d55b`, v1 |
| `Representation.Smooth.Definitions` | `665022df-625b-44ae-9dbd-425f6e266bab`, v1 |
| `Representation.Smooth.SmoothPart.Definitions` | `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, v1 |
| `Representation.Smooth.Contragredient.Definitions` | `be3f8221-aa6f-4069-8faa-f04e1f5dc4b7`, v1 |
| `Representation.Classification.ConstituentRelations` | `6e37a13c-981a-4b66-89fe-9f6852097fad`, v1; independently accepted and published in the current Library. |

The final aggregate was checked by `lean_check`, diagnostic
`b243f60b-5778-48ba-9958-205d01aa6872`, with zero errors and warnings.
Inspection returned `statement_returns_prop: true` and the whole-target
fingerprint
`9eb7aa6cc3026f8921e6f20e9f8966e6afec3e4ce62b8b829d7d0aedecd007fa`.
The elaborated component definitions were also printed with explicit
universes: the field universe and carrier universe are independent.
These are development checks, not proof or semantic acceptance.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` v1,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
This family is a concrete prerequisite, not completion of the assigned
segment/tempered/unitary-generic classification. In particular, it has no
induction functor, supercuspidality predicate, segment or multisegment data,
genericity predicate, or square-integrability/temperedness classification.
Those interfaces retain their assigned owners and must be integrated into
the remaining statements.
