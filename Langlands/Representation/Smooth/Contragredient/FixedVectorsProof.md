# Fixed smooth functionals: implemented proof

`Langlands.smoothDualFixedVectors` proves all four clauses of the published
`Langlands.SmoothDualFixedVectorsStatement` in
[FixedVectorsStatement](FixedVectorsStatement.md).
Worker 0 authored the proof terms and the initial explanation. Worker 59
verified the Library imports and original source context, retained those
proof terms, and expanded this explanation for submission.
The two evaluation formulas are definitional. Extensionality on the two
linear maps reduces the factorization formula to the same evaluation.
For naturality, evaluating either side at a fixed smooth functional `ell`
and a fixed vector `v` gives `ell (f v)`, again by definitional equality.

The four component lemmas remain in this proof module:

| Lemma | Implemented proof |
| --- | --- |
| `smoothDualFixedEquiv_apply` | The open-subgroup equivalence forgets the smoothness witness while retaining the same functional. Its evaluation equals `smoothDualPairing`, by `rfl`. |
| `smoothDualFixedRestriction_apply` | Restriction composes the underlying functional with the fixed-submodule inclusion. Evaluation is therefore the original pairing on that vector, by `rfl`. |
| `smoothDualFixedRestriction_factor` | `ext ell v` reduces equality of the linear maps to evaluation on a functional and a fixed vector. The equivalence and inclusions preserve these values; `rfl` closes the goal. |
| `smoothDualFixedRestriction_natural` | `ext ell v` reduces both sides to `ell (f v)`; `rfl` closes the goal. |

In the naturality equation, `f : rho -> sigma` induces pullback
`contragredientMap f` from smooth functionals on `sigma` to those on `rho`.
The map `fixedVectorsMap f K` goes from fixed vectors of `rho` to those of
`sigma`; its linear dual reverses this direction. Openness is required for
the fixed-functional equivalence and factorization. Restriction and its
naturality apply to every subgroup.

The closing theorem uses `omit [IsTopologicalGroup G]`, introduces the
topological-group instance inside the target, and supplies all four lemmas.
No averaging, finite-dimensional duality, or prior project theorem
is used. Its only direct import is the adjacent proposition module, with
construction dependencies documented there.

This internal proof concerns the elementary maps underlying Casselman
Chapter II, revision June 16, 2019, Section 3, page 6, opening paragraphs
and Proposition II.3.1:
`casselman-2019-smooth-representations`, SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
It does not prove that proposition's isomorphism assertion.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.
The source defines the smooth contragredient and states compact-open
fixed-vector duality under its ambient hypotheses. These four elementary
identities use only the explicit maps, which justifies their broader scope;
they assert neither injectivity nor surjectivity of restriction.

The target `Langlands.SmoothDualFixedVectorsStatement` is in the published
`Langlands.Representation.Smooth.Contragredient.FixedVectorsStatement`.
Its construction imports are
`Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions` and
`Langlands.Representation.Smooth.FixedVectors.Definitions`; their transitive
imports supply smoothness, smooth parts and the dual constructions. The
published target and all its project Lean imports match the checked source files.
The transitive project imports are `Langlands.Representation.Dual.Definitions`,
`Langlands.Representation.Smooth.Definitions`,
`Langlands.Representation.Smooth.SmoothPart.Definitions`,
`Langlands.Representation.Smooth.Contragredient.Definitions`, and
`Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions`.
This elementary proof does not depend on the separate compact-duality or
reflexivity proofs, both of which are implemented in the Library.

In [CompactDualityProof](CompactDualityProof.md),
`Langlands.smoothDualCompactFixedDuality` proves
`SmoothDualCompactFixedDualityStatement`: restriction is bijective for a smooth
complex representation and one specified compact open subgroup. Its inverse
extends a functional by composing it with finite-orbit averaging. This requires
neither admissibility nor compact-open cofinality.

In [AdmissibleDualityProof](AdmissibleDualityProof.md),
`Langlands.smoothAdmissibleDuality` proves
`SmoothAdmissibleDualityStatement`. It assumes compact-open cofinality:
every open subgroup contains an open subgroup whose underlying set is compact.
Under that assumption, the canonical `smoothBidual` is injective for every
smooth complex representation. For an admissible representation, its smooth
contragredient is admissible and the same canonical map is bijective.
Here admissibility means smoothness and finite-dimensional fixed vectors for
every open subgroup. Injectivity alone does not require admissibility. Both
duality targets retain independent group and carrier universes `uG uV` and
quantify the topological-group instance inside the proposition.

The admissible-duality proof uses compact-fixed restriction to extend
functionals and separate vectors, the cofinal admissibility criterion to
transfer finite dimension, and finite-dimensional algebraic reflexivity on a
compact-open fixed space to represent each smooth bidual functional. These
results correspond to Casselman II.3.1 and the following admissibility argument,
and Lemma II.3.2 on page 6. The lemma's freeness condition is automatic over
the complex numbers; separation for every smooth representation is a derived
consequence of compact duality and algebraic dual separation. The explicit
cofinality hypothesis replaces the source's stronger ambient group assumptions.
None of these arguments is needed for the four elementary identities here.

All four component laws and the closing theorem remain one proof contribution.
The coefficient ring, group and two representation carriers have independent
universes `uR uG uV uW`. Coefficients form an arbitrary commutative ring.
The topological-group hypothesis is inside the proposition. No original
smoothness, admissibility, compactness, finite dimension, characteristic-zero
or Noetherian assumption is added. No topology is imposed on the coefficients
or modules. The full declaration type, including its outer parameters, is
retained.

Worker 320 checked the status, hypotheses and imports against Library
`fb40559309dd366f4145aa31aad8c3db11b7cc07`, without changing any Lean source.
The compact-duality implementation is distinct from its historical independent
acceptance record, which was not verified in this correction. For admissible
duality, independent approval is recorded by review
`40cf4bc6-85b4-42c5-93eb-ee31e50a6077` of proof
`81c91e2f-1a4d-45f0-98f2-0710f820d150`, published at
`196ceda926c7cfe1fdbe5ae57c08133d83bbf940`. Compilation and declaration
inspection remain distinct from independent semantic acceptance.
