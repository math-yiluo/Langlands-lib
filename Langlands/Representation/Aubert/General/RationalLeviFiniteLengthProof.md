# Finite length inside actual standard Levis

Authors: Worker 1343 and Worker 1254. Assembly and dependency account checked
by Worker 158.

`rationalLeviFiniteLengthStatement` proves the whole published proposition
`RationalLeviFiniteLengthStatement.{u, v}` from
`RationalInvolutivityReduction`. It has no additional theorem parameters.
It pairs `standardLeviInduction_preservesFiniteLength` with
`standardLeviJacquet_preservesFiniteLength` for every standard subset `J`
and every `I : Finset J`. Both use the canonical evaluation topology and
the literal parabolic, Levi and radical subgroups of rational points.
The field and representation universes remain independent, and the
representation carriers have universe `max (u + 1) v`.

This is an internal deduction from the proposition's displayed ambient
finite-length and topological premises, rather than an additional
literature assertion. The proof introduces all of those premises, uses
closedness to equip each standard Levi with its locally compact topology,
and applies the two imported preservation proofs. The root-label type
need not be nonempty or have a chosen enumeration. Thus the proof includes
empty `J`, empty `I` and an empty simple-root type. It retains the target's
full connected-reductive scope over nonarchimedean local fields, including
positive characteristic, nonsplit and non-quasisplit groups. The structural
statements, closedness, projection continuity, compact-limit and ambient
preservation premises remain exactly the displayed premises of the target.

The induction half uses ordinary smooth induction in stages, its split
quotient comparison, normalization by inverse character twisting, and
finite-length reflection. The Jacquet half uses surjective evaluation on
actual induction and the resulting scalar-intertwining quotient of
ambient coinvariants. The imported paired Markdown explains these
arguments at declaration level.

The proof does not invoke a Langlands classification, character independence,
the geometric lemma or a cuspidal-support theorem. Its adjointness-related
dependency is the explicit evaluation map and covariance in
`FirstAdjointness`, used by `StandardLeviJacquetFiniteLength`; it does not
assume an adjointness theorem as a new premise. The induction half reuses
the generic algebraic finite-length transport declarations in
`Classification/FiniteLengthProof`; those transport lemmas themselves do
not use classification.

This proves the inside-Levi preservation input needed for the rational
corollary and involutivity reductions. Induction compatibility and
Corollary 1.10(a) remain separate obligations.

The following declaration-level dependencies account for the potentially
misleading source-module names. Declaration types and proof bodies use only
the indicated elementary results from these modules.

| Used declarations | Actual content and scope |
| --- | --- |
| `Langlands.FiniteLengthAssembly.finiteLength_of_surjective` | A surjective intertwiner is a surjective group-algebra linear map, so finite length descends. It applies to arbitrary representations over a field and a monoid; it invokes no classification. |
| `Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff` and `Langlands.FiniteLengthAssembly.length_comp_surjective` | Composition with a surjective monoid homomorphism preserves the submodule lattice and hence module length. They are generic algebraic lemmas in `Classification/FiniteLengthProof`. |
| `Langlands.CuspidalSupport.JacquetLength.compSubrepresentationOrderIso` | This is the underlying invariant-subspace order isomorphism used by `length_comp_surjective`, for arbitrary monoids and a surjective homomorphism. Its occurrence in `CuspidalSupport/InducedJacquetCount` introduces no cuspidal-support theorem. |
| `Langlands.Aubert.General.FirstAdjointness.evaluation` and `Langlands.Aubert.General.FirstAdjointness.evaluation_covariance` | Explicit evaluation at the identity and the covariance formula, through `Langlands.Jacquet.CharacterReciprocity.evaluation`, `evaluation_covariance` and `evaluation_translate`. The proof uses these actual constructions, with no adjunction equivalence as a premise or transitive theorem dependency. |
| `Langlands.GroupScheme.adjoint` and `Langlands.GroupScheme.lieKernelConjugationLinear` | The scheme-level conjugation action underlying the actual relative-root data; these are unrelated to adjointness of induction and Jacquet functors. |

The imported `RationalInvolutivityReduction` supplies the target proposition;
its conditional involutivity theorem is not used. Imports include other
classification and cuspidal-support modules transitively, but the proof uses
only the generic declarations just listed from those modules. The detailed
ordinary-stages, topology, twisting, finite-length-reflection and coinvariant
dependencies are described in the two helper Markdown files.
