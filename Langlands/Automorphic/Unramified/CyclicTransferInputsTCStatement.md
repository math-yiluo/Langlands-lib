# Totally complex forms of the cyclic transfer inputs of Harris's Proposition 4.8

**Scope.** The module
`Langlands.Automorphic.Unramified.CyclicTransferInputsTCStatement` defines four
propositions in the namespace `Langlands.Automorphic.Unramified` and proves
nothing. Each is a published proposition with one more instance argument,
`[NumberField.IsTotallyComplex F]`, inserted directly after `[NumberField F]` for
the base field `F`. The universe parameters are the same, and the rest of each
body is copied verbatim. The extension field `E` gets no new argument: it is then
totally complex automatically (§2).

| Harris input | New proposition | Universes | Published original | Original module |
|---|---|---|---|---|
| 11 | `CyclicRegularInductionTCStatement` | `uF uE uV uW` | `CyclicRegularInductionStatement` | `Langlands.Automorphic.Unramified.CyclicTransferStatement` |
| 12 | `CyclicRegularOrbitLiftTCStatement` | `uF uE uV uW` | `CyclicRegularOrbitLiftStatement` | `Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement` |
| 13 | `CyclicStableDescentTCStatement` | `uF uE uV uW` | `CyclicStableDescentStatement` | `Langlands.Automorphic.Unramified.CyclicTransferStatement` |
| 14 | `CyclicWeakInductionSupercuspidalTCStatement` | `uF uE uV uW` | `CyclicWeakInductionSupercuspidalStatement` | `Langlands.Automorphic.Unramified.CyclicWeakInductionSupercuspidalStatement` |

The input numbers are those of the conjuncts of
`Langlands.Global.Harris.Proposition48ReductionStatement`. The principal
declaration of the module is
`Langlands.Automorphic.Unramified.CyclicRegularInductionTCStatement`.

## 1. The statements

All vocabulary is that of the originals, and nothing is redefined:
`HeckeCharacter.HasNormKernel`, `IsoClass.IsWeakInductionOf`,
`IsoClass.IsWeakBaseChangeOf`, `IsobaricData.IsWeakBaseChangeOf`,
`IsobaricData.galoisOrbit`, `IsoClass.IsFiniteOrderDeterminantTwist`,
`IsGaloisStable`, `IsGaloisConjugate` and `HasSupercuspidalComponent` are explained
in `CyclicTransferStatement.md`, `IsobaricCyclicTransferStatement.md` and
`CyclicWeakInductionSupercuspidalStatement.md`. In each statement `F` and `E` are
number fields with `E/F` Galois, both adele quotients compact, and `F` totally
complex. In words:

- `CyclicRegularInductionTCStatement` (input 11). Let `E/F` be cyclic of degree
  `ℓ` with generator `σ`, and `η` a Hecke character of `F` with norm kernel `E`.
  A cuspidal `T` of rank `m + 1` over `E` with unitary central character that is
  isomorphic to none of its conjugates by `σ^i`, `0 < i < ℓ`, is weakly
  automorphically induced to a cuspidal class `c` of rank `(m + 1) ℓ` over `F`;
  `c` is the only class weakly induced from `T`, and `c ≅ c ⊗ η`.
- `CyclicRegularOrbitLiftTCStatement` (input 12). For the same data, there is a
  cuspidal class `c` over `F` of rank `(m + 1) ℓ`, unitary as an isobaric datum,
  with `c ≅ c ⊗ η`, such that a unitary isobaric datum over `F` has the Galois
  orbit `T ⊞ T^σ ⊞ ⋯ ⊞ T^{σ^{ℓ-1}}` as weak base change exactly when it is `c`.
- `CyclicStableDescentTCStatement` (input 13). A cuspidal `T` over `E` with
  unitary central character that is stable under `σ` is the weak base change of a
  class `c` over `F`; the classes over `F` of which `T` is the weak base change are
  exactly the twists `c ⊗ η^i`, `0 ≤ i < ℓ`; and these twists are pairwise
  distinct.
- `CyclicWeakInductionSupercuspidalTCStatement` (input 14). Let `E/F` be cyclic of
  prime degree with generator `σ`, `v` a finite place of `F` with exactly one
  place `w` of `E` above it, `S` a cuspidal realization over `F` and `T` one over
  `E` with unitary central character and a presentation whose component at `w` is
  supercuspidal. If, for each `0 < i < [E : F]`, some conjugate of `T` by `σ^i`
  has a presentation whose component at `w` is supercuspidal and inequivalent to
  that of `T`, and if `S` is weakly induced from `T`, then `S` has a supercuspidal
  component at `v`.

## 2. Effect of the restriction

Every finite extension of a totally complex field is totally complex (Mathlib
`NumberField.isTotallyComplex_of_algebra`), so under the new instance `E` is
totally complex too. The bodies have no archimedean clause: the weak relations
compare Hecke data at almost all finite places, and input 14 concerns one finite
place. The restriction therefore changes only the class of base fields, and
nothing in the bodies becomes vacuous. Its purpose is the proof. Over a totally
complex `F` every infinite place `v` of `F` is complex and splits completely in
`E` (`E ⊗_F F_v ≅ ℂ^ℓ`), so the archimedean places enter Arthur and Clozel's
trace-formula comparison only as split places, and no base change for `GL_n(ℝ)`
or across `ℂ/ℝ` is needed.

## 3. Relation to the originals

Each original implies its totally complex form at the same universe levels: apply
it to the same fields and forget the new instance. A development check outside
the module compiled the four implications, each as `fun h F E _ _ _ => h F E`. The
converses are not claimed. The statements make no claim about extensions whose
base field has a real place.

## 4. Why the totally complex forms are stated

Harris's Proposition 4.8 (published as `Langlands.Global.Harris.Proposition48Statement`)
concerns CM fields: in a `Proposition48Problem` the fields `E` and `E'` are CM and
`L` is a finite extension of `E`. Its proof applies the cyclic inputs to prime
cyclic steps between intermediate fields of these extensions, in the prime and
singleton branches (inputs 5 and 6). A CM field is totally complex (Mathlib
`NumberField.IsCMField.isTotallyComplex`), and so are all its finite extensions.
The totally complex reduction
`Langlands.Global.Harris.Proposition48ReductionTCStatement` (module
`Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement`) takes these
forms, at universes `{0, 0, uV, uV}`, as its inputs 11–14.

The unrestricted statements remain in the Library as infrastructure.

## 5. Sources and provenance

Provenance: *derived*. The propositions are the special cases, for totally complex
base fields, of the published statements, which follow the sources below; the
sources state their results for every number field (input 14: for every
non-archimedean local field). The sources and locators are those of the originals;
the full correspondence, the conventions and the source gaps (including the
misprints noted there) are in the three Markdown files named in §1.

- `arthur-clozel-1989-base-change` (AC89): J. Arthur and L. Clozel, *Simple
  Algebras, Base Change, and the Advanced Theory of the Trace Formula*, Annals of
  Mathematics Studies 120 (1989), Chapter III (PDF page = printed page + 14):
  Definition 1.1, printed p.199 (PDF 213): weak base change; Definition 4.1 and
  Theorem 4.2 (d), (e), printed pp.202–203 (PDF 216–217); Definition 6.1,
  Theorem 6.2 and Lemmas 6.3 and 6.4, printed pp.215–217 (PDF 229–231). Inputs
  11–13.
- `henniart-herb-1995-induction` (HH95): G. Henniart and R. Herb, *Automorphic
  induction for GL(n) (over local non-archimedean fields)*, Duke Math. J. 78
  (1995), 131–192, Proposition 5.5, printed pp.152–153 (PDF 22–23). Input 14.
- `harris-1998-local-langlands` (Harris): M. Harris, *The local Langlands
  conjecture for GL(n) over a p-adic field, n < p*, Invent. Math. 134 (1998),
  177–210, proof of Proposition 4.8, printed pp.202–203 (PDF 26–27): the
  application of these inputs, over CM fields and their extensions.
