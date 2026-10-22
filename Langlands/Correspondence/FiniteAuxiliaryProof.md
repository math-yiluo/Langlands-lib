# Finite auxiliary arguments for constructing correspondences

This file accompanies the proof of the complete Library proposition
`Langlands.Henniart.FiniteAuxiliaryStatement`. Worker 0 supplied the Lean proof;
Worker 29 checked its argument, Mathlib dependencies, original-source provenance
and full target, and expanded this explanation. Worker 30 authored the published
statement. The statement and its import closure are unchanged.
The proof imports the published canonical module
`Langlands.Correspondence.FiniteAuxiliaryStatement`; the declaration namespace
remains `Langlands.Henniart`.

The closing theorem `Langlands.Henniart.finiteAuxiliary` has exactly the original
telescope: nine arbitrary types `X`, `Y`, `T`, `S`, `R`, `I`, `U`, `F`, `K`,
each in its own universe, followed by `Group U`, `MulAction U X`,
`MulAction U Y`, `Field F`, `Field K`, and `Algebra F K`. It conjoins the
following six reusable theorems in the statement's original order.

**`finiteSeparation`.** For a finite candidate set `P : Set X`, put a finite
type structure on its subtype using `Set.Finite.fintype`. Consider the finite
subtype of ordered pairs in `P × P` with unequal entries. The pairwise separation
hypothesis supplies a test for each such pair. Classical choice defines `pick`
on this subtype; `Finset.univ.image pick` is the finite test family. If two
members `x, y` agree on every chosen test but are unequal, their ordered pair
belongs to this subtype. Its chosen test belongs to the image, and its choice
specification contradicts that agreement. The choice is defined only on
distinct pairs. An empty or singleton candidate set therefore needs no witness
in `T`, and the theorem assumes neither `Inhabited T` nor global finiteness of
`X`. The value type `R` is arbitrary and may itself be a function type.

**`finiteTestLifting`.** The chosen tests are already a `Finset T`. On the
finite subtype of its elements, choose a preimage under `project : S → T`
using the supplied preimage hypothesis. Take the finite image of this choice.
Membership in that image gives a chosen test and hence proves that every lift
projects into the test family. Conversely, the chosen lift of any test belongs
to the image and projects to that test. There is no choice of a preimage for
tests outside the prescribed family, and no assumption that `S` is inhabited.
The empty test family gives an empty image.

**`finiteLiftedSeparation`.** Apply `finiteTestLifting` to obtain containment
and coverage. For two candidates agreeing after evaluation through every chosen
lift, select a covering lift for each original test and rewrite using its
projection equality. This gives agreement on the original separating family,
so the given separation hypothesis proves equality. This component needs no
finiteness assumption on the candidate set: a finite separating test family was
already supplied. The preimage hypothesis remains an explicit premise.

**`finiteGaloisEnlargement`.** For `fields : Finset (IntermediateField F K)`,
use the assumptions to supply `FiniteDimensional F E` and `IsGalois F E` locally
for each member of its finite subtype. The witness is the actual intermediate
field

```lean
L := ⨆ E : fields, E.val
```

Finite dimensionality follows from
`IntermediateField.finiteDimensional_iSup_of_finite`. The two instance fields
of `IsGalois` are supplied by `IntermediateField.isSeparable_iSup` and
`IntermediateField.normal_iSup`, using the separability and normality of each
input. The empty constructor `⟨⟩` in the proof builds this class from those
instances; it does not leave an obligation or assume the conclusion.
`le_iSup` puts every input field inside `L`. In the empty-family case the
supremum is the bottom intermediate field, the embedded base field. These
instances require no finiteness, algebraicity, Galois property or algebraic
closure of the ambient extension `K/F`.

**`finiteCounting`.** View `f` on the source set `A` as a function with an
explicit membership argument. `Set.surj_on_of_inj_on_of_ncard_le` takes this
function, its image-containment and injectivity proofs, the inequality
`B.ncard ≤ A.ncard` obtained from the given equality, and the supplied
finiteness of `B`. It returns a preimage with equality in the reverse
orientation; symmetry gives the required `Set.SurjOn` witness. The theorem's
original `A.Finite` hypothesis is introduced as `_hA` and retained in the
statement, although the Mathlib lemma already derives source finiteness from
the injection into the finite target. No conclusion is inferred from equality
of natural cardinalities of two infinite sets.

**`finiteOrbitCounting`.** Given `y : Y`, choose `u : U` and `i : I` such that
`u • y` belongs to `target i`. Apply `finiteCounting` with the stated finite
sets, their equal counts, the restriction of global injectivity, and the
stratum-containment hypothesis. It gives `x` with `f x = u • y`. Then
`u⁻¹ • x` maps to `y`: equivariance, this equality, and `inv_smul_smul`
give `f (u⁻¹ • x) = u⁻¹ • (u • y) = y`. The source strata need not be stable
under the action. No finiteness of any ambient type, freeness, or uniqueness
of stratum representatives is used.

The relevant Mathlib implementation was read in the pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`: `Data/Set/Card.lean`, lines 950–969;
`FieldTheory/IntermediateField/Adjoin/Basic.lean`, lines 76–85 and 130–139;
`FieldTheory/SeparableClosure.lean`, lines 230–235;
`FieldTheory/Normal/Basic.lean`, lines 96–115; and
`FieldTheory/Galois/Basic.lean`, the definition of `IsGalois` and its instance
projections at lines 54–70. These are ordinary proved Mathlib results and
construction classes, rather than additional project assumptions.

The intended application comes from two original sources, whose cited pages
Worker 29 read directly and checked visually:

- Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
  corps p-adique* (2000), §4.3, printed pp.452–453 (PDF pages 14–15).
  The argument selects finitely many separating tests, lifts them using lower
  ranks, and takes a common compositum of auxiliary extensions.
  Registered source `henniart-2000-simple-proof`, retained at
  `/home/taskhub/central-library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`,
  SHA256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Henniart, *La conjecture de Langlands locale numérique pour GL(n)* (1988),
  §2.8, printed pp.506–507 (PDF pages 11–12), especially the concluding
  bijectivity argument on p.507. Finite equal counts upgrade the normalized
  injections to bijections and yield surjectivity of the original injections.
  Registered source `henniart-1988-numerical`, retained at
  `/home/taskhub/central-library/Henniart--La conjecture de Langlands locale numerique pour GL(n)--1988.pdf`,
  SHA256 `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.

These are the provenance of the elementary generalizations already expressed
in the Library statement. The Lean proof does not prove the local candidate
set is finite, the local converse theorem, lower-rank parameter lifting,
conductor-count identities, compatibility of actual unramified twists,
globalization comparisons, rank induction or the local Langlands correspondence.
Those substantive application hypotheses must be established separately.

Worker 29 checked the canonical statement and proof using the project's Lean
service in the prepared Lean 4.34.0 environment with the pinned Mathlib commit
above. The incremental Lake build completed with exit code zero, no errors and
no warnings. A private diagnostic module directly assigned the unapplied
`@Langlands.Henniart.finiteAuxiliary` to the complete nine-universe telescope.
The printed closing and component types retain the original hypotheses.
Inspection of all seven declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`. The closing theorem's inspected universe
parameters are exactly `uX`, `uY`, `uT`, `uS`, `uR`, `uI`, `uU`, `uF`, `uK`.

These checks followed the independently published relocation of the statement
to its canonical module. The canonical Lean file retains SHA-256
`24f6ee46420d7b901c2adc7ff882bffb8ee3b1acc9f52d693519834fca86ec8c`;
both the canonical pair and the compatibility re-export match the Library
base used for this proof. Only the proof's import changed from the supplied
draft. Development checks establish compilation and the inspected types;
independent proof review and publication are separate requirements.
