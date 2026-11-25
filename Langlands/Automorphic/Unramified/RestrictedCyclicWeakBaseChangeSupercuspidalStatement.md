# Supercuspidality descends from a cuspidal weak base change supercuspidal at two places

The module
`Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeSupercuspidalStatement`
defines two propositions in the namespace `Langlands.Automorphic.Unramified`.
Both have universe parameters `uF uE uV uW`, the same as B5:

- `RestrictedCyclicWeakBaseChangeSupercuspidalStatement`, interface B5r, the
  restricted form of B5 for the simple-trace-formula route of Section 5;
- `RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement`, its totally complex
  form.

Both are unproved proposition definitions of a *derived global input*. The
module proves nothing. B5r is meant to be proved with the twisted simple
trace formula.

## 1. The statement

`RestrictedCyclicWeakBaseChangeSupercuspidalStatement` has the binders and
hypotheses of B5 (`CyclicWeakBaseChangeSupercuspidalStatement`, module
`Langlands.Automorphic.Unramified.CyclicWeakBaseChangeSupercuspidalStatement`),
in the same order. It adds one instance, a second place and one local
hypothesis. In full, it quantifies over:

- number fields `F : Type uF` and `E : Type uE`, an algebra `F → E` with
  `[IsGalois F E]`, the instance `[IsUnramifiedAtInfinitePlaces F E]` (new,
  Section 2), and the instances `CompactSpace (AdeleQuotient F)` and
  `CompactSpace (AdeleQuotient E)`, as in B5;
- a proof that `Module.finrank F E` is prime, as in B5, so `E/F` is cyclic of
  prime degree `ℓ`. No generator is chosen;
- a finite place `v : FinitePlace F` and `w : FinitePlacesAbove E v` with
  `∀ w'' : FinitePlacesAbove E v, w'' = w`, as in B5. So `w` is the unique
  place of `E` above `v`;
- (new) a second finite place `v' : FinitePlace F` and
  `w' : FinitePlacesAbove E v'`, with `v' ≠ v` and
  `∀ w'' : FinitePlacesAbove E v', w'' = w'`. So `w'` is the unique place of
  `E` above `v'`;
- a common index `r : ℕ` (rank `r + 1`), cuspidal realizations
  `S : CuspidalOperatorRealization F r` and
  `T : CuspidalOperatorRealization E r`, and one genuine spectral presentation
  `P : CuspidalSpectralPresentation.{uE, uW} T`, as in B5.

The hypotheses are:

1. `ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S`, as in B5;
2. `(P.localComponent w.1).IsSupercuspidal`, as in B5;
3. (new) `(P.localComponent w'.1).IsSupercuspidal`: the local component of the
   *same* presentation `P` at `w'` is supercuspidal;
4. `IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass`: the
   class of `T` is a weak base change of the class of `S` (Arthur–Clozel
   III.1.1; the direction is explained in the Markdown of B5), as in B5.

The conclusion is that of B5 at `v`:
`IsoClass.HasSupercuspidalComponent.{uF, uV} S.isoClass v`.

In words: let `E/F` be cyclic of prime degree, unramified at the infinite
places, and let `v ≠ v'` be finite places of `F`, each with only one place of
`E` above it, `w` and `w'`. If a cuspidal class over `F` with unitary central
character has a cuspidal weak base change to `E` that is supercuspidal at `w`
and at `w'`, then the class is supercuspidal at `v`. This is B5r: the
hypotheses of B5, and a second finite place `v'` of `F`, different from `v`,
with a place `w'` of `E` above it at which the cuspidal weak base change is
supercuspidal; the conclusion of B5 at `v`.

### Why one presentation carries both local hypotheses

Hypotheses 2 and 3 are about the one presentation `P`. A cuspidal realization
has all its local components irreducible in a suitable presentation
(`cuspidalAllLocalIrreduciblePresentationExistence`), and the class of an
irreducible local component does not depend on the presentation
(`CuspidalSpectralPresentation.localComponent_isoClass_eq`, module
`Langlands.Automorphic.AssociatedPresentationComparison`). So a consumer that
knows supercuspidality at `w` and at `w'` from two presentations can pass to
one presentation. The statement does not need two presentation binders.

## 2. Restrictions, and why the proof needs them

B5r is stated as generally as the proof route of Section 5 gives it. Beyond
the second place it has exactly two restrictions, both needed by that proof:

- **`w'` is the unique place above `v'`.** The twisted pseudo-coefficient sits
  at `w'`. If `v'` split in `E`, the component of `T` above `v'` would be a
  tensor product over several places, and the proof would need a separate
  tensor-product bridge for the twisted trace at a split place. The consumer
  needs no more: its validity data give a unique place of the top field above
  the conjugate place `v'` as well as above `v` (Section 4).
- **`[IsUnramifiedAtInfinitePlaces F E]`, general form only.** This is
  Mathlib's class in the root namespace
  (`Mathlib/NumberTheory/NumberField/InfinitePlace/Ramification.lean`): every
  infinite place of `E` is unramified over `F`, so every infinite place of `F`
  splits completely in `E`. Without it, a real place
  of `F` that becomes complex in `E` would need base change from `GL_n(ℝ)` to
  `GL_n(ℂ)` and twisted Harish-Chandra regularity at that place. The program
  does not provide these.

## 3. The totally complex form

`RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement` repeats the general
statement at the same universe levels with two changes:

- the instance `[NumberField.IsTotallyComplex F]` is inserted directly after
  `[NumberField F]`, the convention of B5's TC form and of
  `CyclicTransferInputsTCStatement`;
- `[IsUnramifiedAtInfinitePlaces F E]` is omitted. Over a totally complex `F`
  every infinite place is complex, and an infinite place of `E` above a
  complex place is unramified (Mathlib
  `NumberField.InfinitePlace.isUnramified_iff`). So the instance holds anyway,
  and leaving it out loses nothing.

The general statement implies the TC form: apply it to the same fields after
deriving the instance as just explained. A private development check
compiled this implication, with the instance given by
`⟨fun _ => NumberField.InfinitePlace.isUnramified_iff.mpr
(Or.inr (NumberField.IsTotallyComplex.isComplex _))⟩`. The converse is not
claimed.

## 4. Relation to B5 and to its consumer

- **B5 implies B5r.** Drop the second place and hypothesis 3, and forget the
  instance `[IsUnramifiedAtInfinitePlaces F E]`. The same holds for the TC
  forms. A private development check compiled both implications
  (`fun h F E … hp v w hw v' w' _ _ r S T P hS hPw _ hBC =>
  h F E hp v w hw r S T P hS hPw hBC`). The converse is not claimed.
- **Canonical B5 stays.** B5 and its TC form (module
  `Langlands.Automorphic.Unramified.CyclicWeakBaseChangeSupercuspidalStatement`)
  stay unchanged. The branches do not use B5. Its intended proof is only a
  conditional derivation from the general Arthur–Clozel III.5.1 premise at `v`
  together with E2.
- **Consumer.** The singleton branch of Harris's Proposition 4.8 under the
  exact-stabilizer condition, and its TC form, use B5r with `v` the auxiliary
  place `Q.Ps.v` and `v'` its conjugate `conjPlace Q.E Q.Ps.v` (module
  `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerRestrictedDescentStatement`).
  There `v ≠ v'` because `v` lies over a place split in the imaginary
  quadratic field `K₀`. The uniqueness of `w` and `w'` comes from
  `HasUniquePlaceAbove` for the top field at both places. The child's
  constituent is conjugate self-dual and supercuspidal at `w`, hence also at
  `w'`. The base field there is CM, hence totally complex.

## 5. Why a second place, and proof obligations

The simple-trace-formula route uses two places: a
supercuspidal test at one place for the cuspidal spectral side and regular
elliptic support at another for the geometric side. If `w` is used for the
supercuspidal test, B5 does not guarantee another place where the twisted
character of the base change is nonzero on the σ-regular elliptic set. If the
character vanishes there, every test supported there has zero twisted trace
on that local factor.

The vanishing argument in Arthur–Clozel I.2.11 applies to twisted induction
from σ-stable data on a proper Levi. Ordinary proper parabolic induction is
not enough. For example, over a quadratic extension of non-Archimedean local
fields of characteristic zero, take a unitary character `χ` of the upstairs
multiplicative group with `χ ≠ χ^σ`. The irreducible tempered principal series
`χ × χ^σ` is a local base-change lift (I.6.2(b)). The two distinct inducing
characters are interchanged by σ, so the series is σ-discrete by I.2.8, and
its twisted character is not identically zero on the σ-elliptic set by
I.2.12(i).

B5r supplies a supercuspidal factor at `w'` as well as at `w`. Once identified
with the unitary, σ-stable local factor of the base change, the factor at `w'`
is σ-discrete, so its twisted character is not identically zero on the
σ-elliptic set (I.2.12(i)), and it admits a twisted pseudo-coefficient
(I.2.10). The proposed comparison puts the pseudo-coefficient at `w'` and
uses σ-regular elliptic support at `w`.

The eventual proof, along this route, keeps the following obligations. It
names every input it uses.

1. **Unitarity and rigidity.** These are as in obligations 1 and 2 of B5: `T`
   is unitary, and `T` is identified with Arthur–Clozel's global base change
   `Π` of `S` (III.4.2(a), and C2 for strong multiplicity one).
2. **The comparison.** Use a twisted pseudo-coefficient at `w'` and a function
   with σ-regular elliptic support at `w` in the twisted simple trace formula
   for `E/F`. Compare it with the simple trace formula for `F` with associated
   functions. This requires a formula applicable at the two non-split places,
   not just Arthur–Clozel's split-place formula in I.2.5.
3. **Local descent of σ-stable supercuspidal classes.** This is interface E2,
   in the form the proof needs. It is used at `w` and at `w'`.
4. **The fibre statement.** Two cuspidal classes over `F` whose base changes
   agree almost everywhere differ by a twist by a power of `κ`, a character of
   `F^× N(𝔸_E^×) \ 𝔸_F^×`. This is Arthur–Clozel III, Theorem 3.1; see also
   Henniart–Lemaire II.6.11. If the fibre
   statement is not a Library theorem, it is proved or stated as a named
   premise with its source.
5. **Conclusion by orthogonality.** Orthogonality of elliptic characters gives
   `S_v ≅ ρ ⊗ κ^j` with `ρ` supercuspidal. So `S_v` is supercuspidal.
6. **Actual components.** As in obligation 5 of B5: identify the factor of `P`
   at `w` and at `w'` with the irreducible components of `T`, and produce an
   actual presentation of `S` whose component at `v` is `S_v`.

The local maps of E2 may enter the proof. They are never premises of the
statement, which has no local-map parameter.

## 6. Sources and provenance

Provenance: *derived*. The statement is formulated for the trace-formula route
in Section 5, with supercuspidal components at two non-split places. The two
restrictions in Section 2 are those that proof route needs. The sources below
are not proof evidence.

- `operator-external-inputs-plan-2026-11-16`: operator note *Formalizing the
  large external inputs of the local Langlands correspondence for `GL_n`*,
  16 November 2026 (`external-inputs-plan.tex`). Section 2.2, item B5;
  Section 4.6, item (G) for the two places (TeX lines 744–745); and Section
  4.8, singleton case, Remark 4.2, item (3). The note derives its B5 from
  III.5.1 at `v` together with E2 (TeX lines 737 and 914).
  It also says that the classes to which Harris's argument applies are
  supercuspidal at two conjugate places that are non-split (TeX lines 202 and
  758).
- `arthur-clozel-1989-base-change`: J. Arthur and L. Clozel, *Simple Algebras,
  Base Change, and the Advanced Theory of the Trace Formula*, Annals of
  Mathematics Studies 120 (1989). PDF page = printed page + 14. Chapter I:
  Lemma 2.5, printed p.14 (PDF 28), for the split-place formula; Lemma 2.8,
  Corollary 2.10 and Lemmas 2.11–2.12, printed pp.17–19 (PDF 31–33), for
  σ-discreteness, pseudo-coefficients and the twisted-character distinction;
  Theorem 6.2(b), printed p.51 (PDF 65), for the local lift in the example.
  Chapter III: Definition 1.1, printed p.199 (PDF 213); Theorem 3.1 (the fibre
  statement), printed p.201 (PDF 215); Theorem 4.2, printed p.202 (PDF 216).
- `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`:
  G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour
  GL_n en caractéristique non nulle*, Mém. SMF 124 (2011). Chapter II, §6 (a
  global method), II.6.11, printed p.127. This is the technical lemma used in
  the proof of II.6.12.

No source-specific errata file exists in the Library under these source IDs.
The statement adds no `n < p` condition. It makes no claim when `v` or `v'`
splits in `E`, or when an infinite place ramifies.
