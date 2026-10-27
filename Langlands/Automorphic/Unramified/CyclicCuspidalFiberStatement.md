# The direct cyclic cuspidal fiber statement

Worker 44. `CyclicCuspidalFiberStatement` is a proposition definition for
Arthur–Clozel III.3.1 on actual full cuspidal classes with supplied genuine
spectral systems. The analytic theorem remains to be proved.

## Original source and scope

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), Chapter III, Theorem 3.1, printed p.201
(one-based PDF p.215). The chapter's cyclic-extension and Satake conventions
are on printed p.199 (PDF p.213); the pair-L-function background used in the
proof is on printed p.200 (PDF p.214). These original pages were reread,
and the theorem page was visually checked. The registered original is
`arthur-clozel-1989-base-change`, SHA256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.

The source takes two cuspidal representations over the same number field.
Their unramified Satake classes have equal residue-degree powers almost
everywhere. It concludes that the second is the first twisted by a
character trivial on principal ideles and norms from the specified cyclic
extension. The degree need not be prime. The unitary reduction occurs in
the proof and is not a theorem premise. The statement requires no upstairs
automorphic representation.

The Lean domain uses number fields `F : Type uF` and `E : Type uE`, an
`Algebra F E`, `IsGalois F E`, and `IsCyclic (E ≃ₐ[F] E)`. These express a
cyclic extension of arbitrary finite degree; finiteness follows from the
number-field instances. The fields have independent universes. The two
classes belong to the existing
`CuspidalOperatorRealization.IsoClass F r`, so their common actual rank is
`r + 1`. The explicit `CompactSpace (AdeleQuotient F)` hypothesis is
inherited from the actual cuspidal realization and its constant-term
construction. There is no unitarity hypothesis.

Each of the two supplied numerical systems has its own actual
`IsoClass.HasSpectralSystem` witness. Such a witness contains a nonzero
finite slice inside an actual full cuspidal realization, actual smooth
local factors, a genuine restricted tensor presentation, and normalized
spherical Hecke spectra. The two local-factor carrier universes `uS` and
`uT` remain independent of one another and of `uF` and `uE`. These are
supplied presentations: existence for every class and comparison of
independently supplied presentations are separate obligations.

## Direct numerical premise

The internal helper
`Langlands.Unramified.SpectralSystem.SameResidueDegreePowers E s t`
compares two systems over **F**, each of the same rank. It means that for
all finite places `v` outside one finite set:

- `s` and `t` are both defined at `v`;
- for every actual `w : FinitePlacesAbove E v`, the ramification index
  `w.1.asIdeal.ramificationIdx (𝓞 F)` is one;
- the spectra `s(v)` and `t(v)`, each powered by the actual residue degree
  `w.1.asIdeal.inertiaDeg (𝓞 F)`, are equal.

The cofinite quantifier on `v` precedes the two definedness witnesses and
every `w`. In particular, there is one finite base exceptional set,
uniform in the place above. The spectra are the existing unordered
multisets of nonzero complex eigenvalues, with multiplicities; `power` is
the existing multiset power operation. No ordering of eigenvalues, chosen
matrix, or first-trace substitute is introduced.

The source's single residue degree is independent of the place above in
a Galois extension. Quantification over all actual places above expresses
the comparison without choosing one. Requiring ramification index one
spells out the usual cofinite unramified comparison domain: the source
enlarges its finite exceptional set to make `E/F` unramified. The helper
itself does not need cyclicity or the number-field instance for `F`;
the theorem target retains both number fields and the cyclic Galois
hypotheses.

`sameResidueDegreePowers_iff_guarded` proves equivalence with the usual
guarded formulation that quantifies over proofs of definedness. From
explicit definedness, proof irrelevance identifies any such proofs.
Conversely, the proof intersects the guarded cofinite set with the
complements of both finite exceptional sets before choosing the two
definedness witnesses. `SameResidueDegreePowers.symm` swaps the witnesses
and reverses the spectral equality. These are intrinsic properties of the
helper, not proofs of the analytic theorem.

## A common supplied upstairs system

The helper imports the published numerical
`SpectralSystem.IsArithmeticWeakBaseChangeOf` from
`Langlands.Representation.Unramified.WeakTransfer`.
`SameResidueDegreePowers.of_common_weakBaseChange` takes one supplied
upstairs system `a`, and weak comparisons from `s` and `t` to that same
`a`. It intersects the two cofinite base sets. At each retained base place,
both residue-degree powers equal the spectrum of `a` at each place above,
so symmetry and transitivity of equality give the direct power comparison.
Proof irrelevance identifies the two proofs of definedness for `a`;
the ramification-index condition comes from the first weak comparison.
This proof needs no automorphic realization upstairs and no cyclicity.

`CyclicCuspidalFiberStatement.of_common_weakBaseChange` is a conditional
consequence: given a proof of the proposition defined in this file, the
two genuine downstairs attachments, and those two weak comparisons with a
common `a`, it obtains the same norm-trivial full twist conclusion. It
applies the proposition to the numerical helper. The proposition remains
an explicit premise of this lemma; the analytic theorem is not proved.
All four universes, both actual number fields, cyclic Galois hypotheses
and positive rank are retained.

The upstairs system is explicitly shared. Two witnesses of the published
class relation `IsoClass.IsWeakBaseChangeOf` for a common upstairs class
can use different systems upstairs. Neither the numerical helper nor the
conditional consequence identifies those potentially independent
presentations. If a common system also has a genuine upstairs attachment,
the two supplied comparisons witness the class relations, but that
attachment is not needed for this elementary conditional consequence.

## Actual norm-trivial full twist conclusion

The conclusion is existence of `χ : HeckeCharacter F` with
`χ.IsTrivialOnNorm E` and
`IsoClass.IsFiniteOrderDeterminantTwist χ c d`. The character is the
existing continuous complex-unit-valued character on the actual idele
class quotient. Principal-ideles triviality is therefore built into its
domain. `IsTrivialOnNorm` additionally says, for every actual idele class
`x` of `E`, that `χ (ideleClassNorm x) = 1`. The specified extension
remains present in the conclusion.

The imported finite-order bridge proves
`χ ^ Module.finrank F E = 1` from this norm-triviality and hence proves
finite order. Requiring the finite-order twist relation therefore retains
the source conclusion; it does not replace norm-triviality by an
extension-independent finite-order condition.

The imported full class relation has target `d` and source `c`. Its
complete representative criterion requires an actual complex linear
equivalence between representatives, with the following equations:

- the finite action on the target intertwines with the source action
  multiplied by `χ` on the actual finite adelic determinant;
- the compact action has the corresponding scalar on the actual
  infinite embedding of each compact element;
- the action of every element of the whole archimedean enveloping
  algebra intertwines without a scalar.

This is the published right-translation orientation for twisting the
source by `χ`. For finite-order characters the infinite determinant
multiplier is locally constant; the full enveloping equation remains
part of the supplied equivalence. The conclusion concerns the full
cuspidal class, retaining all three operator families. A total twist
operation or a multiplication operator on every form space is not needed
to state this relation between the two supplied classes. The character
need not be unique, since self-twists can occur.

## Provenance and remaining obligations

The target translates III.3.1 to the Library's actual full-class and
supplied-presentation interfaces. The numerical helper and its filter
lemmas are internal formalization content. The explicit rank convention,
compactness hypothesis, genuine attachment witnesses, all-places
quantifier, and actual quotient norm above describe the precise
reformulation.

This file states III.3.1 for those supplied attachments and proves the
intrinsic filter, symmetry and common-system lemmas, together with the
conditional application just described. It does not prove the analytic
cyclic-fiber implication, assert attachment existence, construct
base-change lifts, or compare independent presentations of a common
upstairs class. Passing from two existential weak-transfer witnesses
for a common upstairs class still requires comparison of their potentially
different upstairs presentations. The prime-degree lifting and descent,
strong local compatibility, and general induced or isobaric categories
remain separate statement and construction obligations.
