# The intrinsic Artinian socle bridge

Authors: Worker 864 (Lean proof and initial Markdown draft) and Worker 713
(dependency-audit revision and submission).

`Langlands.Classification.strongIndecomposabilitySocle` proves the published
`StrongIndecomposabilitySocleStatement` with independent universes
`uK`, `uG`, `uH`, and `uV`, in that order. It has no additional hypotheses. The
proof imports the published statement, its intrinsic strong-indecomposability
definition, and the existing `StrongConstituentExtremaProof` interface without
modifying their Lean or Markdown files.

## Declarations

The module declares, in namespace `Langlands.Classification`, with implicit
`k : Type uK` (a field), `G : Type uG` (a group), `V : Type uV` (a `k`-module)
and `ρ : Representation k G V`:

- `unique_atom_of_stronglyIndecomposable [Nontrivial V]
  (hArt : IsArtinian k[G] ρ.asModule) (h : IsStronglyIndecomposable ρ) :
  ∃! S : Subrepresentation ρ, IsAtom S`;
- `stronglyIndecomposable_of_unique_atom (hArt : IsArtinian k[G] ρ.asModule)
  (h : ∃! S : Subrepresentation ρ, IsAtom S) : IsStronglyIndecomposable ρ`;
- `stronglyIndecomposable_of_comp {H : Type uH} [Group H] (f : H →* G)
  (h : IsStronglyIndecomposable (ρ.comp f)) : IsStronglyIndecomposable ρ`;
- `strongIndecomposabilitySocle :
  StrongIndecomposabilitySocleStatement.{uK, uG, uH, uV}`.

## The implemented proof

`unique_atom_of_stronglyIndecomposable` works over an arbitrary field `k`,
group `G`, and nontrivial `k`-module `V`, for `ρ : Representation k G V`.
Artinianity is `IsArtinian k[G] ρ.asModule`, over the actual group algebra.
Through well-foundedness of `<` on submodules, Mathlib's instances make the
lattice of its submodules atomic. The proof explicitly transfers nontriviality
of `V` to `ρ.asModule`, obtains an atom `N` of `Submodule k[G] ρ.asModule` with
`IsAtomic.exists_atom`, and transports it to an actual subrepresentation
through Mathlib's order isomorphism
`Subrepresentation.subrepresentationSubmoduleOrderIso` (and
`OrderIso.isAtom_iff`). For any other atom `T`, strong indecomposability makes
the intersection with this atom nonbottom. `IsAtom.ne_bot_iff_eq` then
identifies that intersection with each of the two atoms, so they are equal as
actual subrepresentations.

`stronglyIndecomposable_of_unique_atom` uses the same order isomorphism
(`OrderIso.isAtomic_iff`) to make the subrepresentation lattice atomic. It
needs Artinianity and a unique atom, but no separate nontriviality premise.
For each nonbottom subrepresentation, `eq_bot_or_exists_atom_le` supplies an
atom below it. Uniqueness places the same nonbottom atom in every two such
subrepresentations, so their intersection lies above it and is nonbottom.

The first clause of `strongIndecomposabilitySocle` packages these two
directions. The second clause applies the unique-atom criterion to a
nontrivial Artinian complex representation, then uses the unique-atom
direction of `strongConstituentExtrema` to obtain
`IsIrreducibleSocle ρ (socleRepresentation ρ)`. This existing theorem retains
an actual injective intertwiner and equality of its linear image with that
of every irreducible embedding whose source lies in the carrier universe.
No isomorphism-class uniqueness replaces this equality of subspaces.

For the third clause, the witness is the actual smooth object
`A.socleSubrepresentation`. Its action is definitionally
`socleRepresentation A.representation`; its carrier remains in `Type uV`.
The same unique-atom result and `strongConstituentExtrema` supply the required
strong socle relation. The input `Nontrivial A` is installed as a local
instance. No continuity of group operations is added to the statement's
topology premise.

`stronglyIndecomposable_of_comp` proves the fourth clause. For any
homomorphism `f : H →* G`, it views each `G`-invariant subspace as invariant
under `ρ.comp f`, retaining its underlying submodule. Injectivity of
`Subrepresentation.toSubmodule` shows that this view preserves the nonbottom
condition and that a zero original intersection would give a zero restricted
intersection. Strong indecomposability of the restriction rules that out.
This proof needs no nontriviality, Artinianity, topology, or condition on `f`.

The final theorem packages the two directions of the criterion, the complex
and smooth socle clauses, and restriction transport into exactly the four
conjuncts of the published statement.

## Source and provenance

Zelevinsky, *Induced representations of reductive p-adic groups II* (1980),
§5.4, printed p.188/PDF25, motivates the finite-length criterion: a
representation of finite length is strongly indecomposable if and only if it
has a unique nonzero irreducible submodule. The registered source is
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The source calls the criterion clear and gives no argument. The implemented
proof is an internal Artinian strengthening over general fields and groups,
with canonical-socle and restriction adapters; these are derived content, not
statements of the source. It uses atomicity of Artinian submodule lattices
rather than a GL-specific argument. The zero representation remains strongly
indecomposable vacuously; clauses 1–3 retain the separate nontriviality
hypotheses already in the statement.

## Dependency audit and scope

The strong-constituent proof constructs actual subrepresentation inclusions
and quotients and applies the generic atom-to-irreducible lemma
`FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom` from
`Category.FiniteIndexRestriction`. Canonical constituents use invariant
subspaces and representation equivalences; smooth subrepresentations use
`Smooth.Transfer.SubquotientProof`.

The complete project import closure of this module has 20 modules:

- this proof, `Classification.StrongIndecomposabilitySocleStatement`, and
  `Classification.StrongIndecomposability`;
- `Classification.StrongConstituentExtremaProof`,
  `Classification.StrongConstituentExtremaStatement`,
  `Classification.CanonicalConstituents`,
  `Classification.ConstituentRelations`, and `Classification.Cosocle`;
- `Representation.SubrepresentationLattice`, `Category.Basic`,
  `Category.Subquotients`, `Category.FiniteIndexRestriction`,
  `Smooth.Definitions`, `Smooth.Transfer.SubquotientStatement`,
  `Smooth.Transfer.SubquotientProof`, and `Twist.Definitions`;
- `Weil.Representation.Basic`, `Weil.Representation.Determinant`,
  `Weil.Representation.Operations`, and
  `Weil.Representation.IsomorphismInvarianceProof`.

Here all but the Weil modules are under `Langlands.Representation`, and the
Weil modules are under `Langlands`. All are generic representation, lattice,
category, smooth-transfer, canonical-constituent, and Weil-representation
interfaces. The closure contains no GL segment, derivative, analytic,
exhaustion, or Langlands classification theorem.

In particular, the proof does not use socle exhaustion, special-head
exhaustion/existence, quotient coverage, tempered uniqueness,
square-integrable classification/exhaustion, or regular exhaustion, including
successor proofs and transitive proof dependencies excluded by the ordered
multisegment socle task. Worker 864 audited the imports against the published
statement and definition before sharing the draft; Worker 713 recomputed the
closure above from the submitted workspace.

This result supplies neither a nonzero carrier nor Artinianity for an actual
induced product and proves no ordered multisegment existence theorem. Those
remain separate inputs. Development compilation and declaration inspection
in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` succeed with no
diagnostics, independent `uK,uG,uH,uV`, and only `propext`, `Classical.choice`,
and `Quot.sound`. Independent semantic acceptance, exact-target validation,
and Library publication remain required for this proof.
