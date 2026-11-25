# Supercuspidality descends from a cuspidal weak base change at a unique place

The module
`Langlands.Automorphic.Unramified.CyclicWeakBaseChangeSupercuspidalStatement`
defines two propositions in the namespace `Langlands.Automorphic.Unramified`,
both with universe parameters `uF uE uV uW`:

- `CyclicWeakBaseChangeSupercuspidalStatement`, interface B5 of the operator's
  plan of 16 November 2026 (Section 2.2);
- `CyclicWeakBaseChangeSupercuspidalTCStatement`, its totally complex form.

Both are unproved proposition definitions of a *derived global input*. The
module proves nothing. The proofs of the canonical statements need the simple
trace formula with its twisted form and local cyclic base change of prime
degree.

## 1. The statement

`CyclicWeakBaseChangeSupercuspidalStatement` quantifies over:

- number fields `F : Type uF` and `E : Type uE`, an algebra `F → E` with
  `[IsGalois F E]`, and the instances `CompactSpace (AdeleQuotient F)` and
  `CompactSpace (AdeleQuotient E)`. The existing cuspidal APIs require these
  compactness instances, which are explicit parameters here as in B1–B4;
- a proof that `Module.finrank F E` is prime. A Galois group of prime order
  is cyclic, so `E/F` is cyclic of prime degree `ℓ`. The statement does not
  mention Galois conjugates, so no generator `σ` is chosen;
- a finite place `v : FinitePlace F` and `w : FinitePlacesAbove E v`, with
  every place of `E` above `v` equal to `w`. So `w` is the unique place of `E`
  above `v`;
- a common index `r : ℕ`, an actual cuspidal realization
  `S : CuspidalOperatorRealization F r` over `F`, an actual cuspidal
  realization `T : CuspidalOperatorRealization E r` over `E`, and a genuine
  spectral presentation `P : CuspidalSpectralPresentation.{uE, uW} T`. The
  index `r` means the positive rank `r + 1`. Base change keeps the rank, so
  `S` and `T` share the same index.

The hypotheses are:

1. `ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S`: `S` has
   a continuous unitary idele-class central character. This is the Library's
   convention for "unitary" cuspidal classes in its operator-realization
   statements (B1–B4, and `CyclicPrimeCuspidalLiftStatement`).
2. `(P.localComponent w.1).IsSupercuspidal`: the local component of `P` at the
   place `w` is supercuspidal.
3. `IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass`: the
   cuspidal class of `T` is a weak base change of the cuspidal class of `S`.

The conclusion is
`IsoClass.HasSupercuspidalComponent.{uF, uV} S.isoClass v`: some actual
spectral presentation of a representative of the class of `S` has a
supercuspidal local component at `v`.

In words: let `E/F` be cyclic of prime degree and `v` a finite place of `F`
with only one place `w` of `E` above it. If a cuspidal class over `F` with
unitary central character has a cuspidal weak base change to `E` that is
supercuspidal at `w`, then the class is supercuspidal at `v`. This is the
literal B5 of the plan: "if a unitary cuspidal class over `F` has a cuspidal
weak base change over `E` whose component at `w` is supercuspidal, its own
component at `v` is supercuspidal". Each clause corresponds to one hypothesis
above.

### Direction of the weak base change

`IsoClass.IsWeakBaseChangeOf d c` (module
`Langlands.Automorphic.Unramified.WeakTransfer`) takes the class `d` over the
extension `E` first and the class `c` over the base `F` second. It says that
`d` is a weak base change of `c`. Some spectral systems `s` of `c` and `t` of
`d`, attached through genuine presentations, satisfy
`t.IsArithmeticWeakBaseChangeOf s`. That relation holds on a cofinite set of
places `v'` of `F` that are unramified in `E`, with every place `w'` above
`v'` defined in `t`. At each such `w'`, the unordered spectrum (Satake
parameter) of `t` at `w'` is the `f(w'|v')`-th power of that of `s` at `v'`, where `f(w'|v')`
is the residue degree. This is Arthur–Clozel's weak lifting, Definition
III.1.1. The application `IsWeakBaseChangeOf T.isoClass S.isoClass` therefore
says that `T` lifts `S` from `F` to `E`. Base change goes up, from `F` to `E`.
Supercuspidality goes down, from `w` to `v`.

### Actual local components

Both local conditions concern genuine local components of cuspidal
realizations. These are `LocalRealization`s, actual embedded local copies of
the factors of a finite tensor presentation inside the cuspidal realization.
`LocalRealization.IsSupercuspidal` (module
`Langlands.Automorphic.SupercuspidalComponent`) requires the realization to
be irreducible and admissible, with its canonical `p`-adic class in the
published Jacquet-vanishing supercuspidal class space. The hypothesis is about
the one supplied presentation `P` of `T`. The conclusion asks for some
presentation of `S`, and by `hasSupercuspidalComponent_iff` any
representative of the class may be used. No local base-change map, local
character identity, or local Galois parameter appears in the statement.

## 2. The totally complex form

`CyclicWeakBaseChangeSupercuspidalTCStatement` repeats the general statement
verbatim, at the same universe levels, with the one instance argument
`[NumberField.IsTotallyComplex F]` inserted directly after `[NumberField F]`.
This follows the convention of `CyclicTransferInputsTCStatement`. `E` gets no
new argument: every finite extension of a totally complex field is totally
complex (Mathlib `NumberField.isTotallyComplex_of_algebra`).

The restriction changes only the class of base fields. The body has no
archimedean clause, and nothing in it becomes vacuous. Its purpose is the
proof. Over a totally complex `F` every infinite place splits completely in
`E`, so Arthur and Clozel's comparison needs no base change for `GL_n(ℝ)` or
across `ℂ/ℝ`. The singleton branch of Harris's Proposition 4.8, which needs
B5, works with prime cyclic steps between finite extensions of CM fields, and
these fields are totally complex.

The general statement implies the totally complex form: apply it to the same
fields and forget the instance. A private development check compiled this
implication as `fun h F E _ _ _ => h F E`. The converse is not claimed.

## 3. A global consequence, not the local theorem

The local base-change theorem of Arthur–Clozel, Chapter I, Section 6, is about
arbitrary irreducible representations of `GL_n(F_v)` and their lifts to
`GL_n(E_w)`. This declaration is not that theorem. It does not mention local
lifts. It concerns only local components of cuspidal classes that are related
globally by the weak, almost-everywhere relation. It neither implies nor
states the local theorem or its fibres. It isolates the consequence at one
non-split place that the singleton branch of Harris's Proposition 4.8 needs:
plan Section 4.8, Remark 4.2 (`rem:noDrinfeld`), item (3) for a fibre with
one element. The plan says this is needed with or without the comparison
interface A2.

Neither of the following proves the conclusion by itself:

- **The weak relation.** It constrains Satake parameters only on a cofinite
  set of unramified places. It carries no information at a single prescribed
  place `v`, and in rank at least two a supercuspidal component is never
  unramified. The information has to come from the global trace-formula
  comparison, through strong lifting.
- **Arthur–Clozel Lemma I.6.10.** It describes the lift of a representation
  that is already supercuspidal. The lift is supercuspidal if it is discrete,
  and otherwise it is `T × T^σ × ⋯` with `T` supercuspidal. B5 needs the
  converse direction: a non-supercuspidal `π_v` never lifts to a
  supercuspidal representation. That requires the lifts of generalized
  Steinberg representations (I.6.12) and of Langlands quotients (the
  extension after I.6.8), together with a count of supercuspidal supports.

## 4. Proof obligations

The statement is derived: Arthur and Clozel do not state it in this form. Its
eventual proof keeps all of the following obligations. Here `ℓ`
is the prime `[E : F]` and `η` is a Hecke character of `F` with norm kernel
`E`. The proof may choose `η`, but the statement does not need one.

1. **Unitarity.** Arthur–Clozel's Chapter III works with representations
   induced from *unitary* cuspidal data (Definition III.4.1). The proof must
   match `HasUnitaryCentralCharacter S` with the unitarity of the cuspidal
   automorphic representation `S`, as in the other operator-realization
   statements. It must also show that `T` is unitary, because `T` carries no
   unitarity hypothesis. A route: the weak relation identifies the central
   character of `T` with `ω_S ∘ N_{E/F}` at almost all places. Rigidity of
   Hecke characters (`HeckeLocalComponentRigidityStatement`) gives equality,
   and `ω_S ∘ N_{E/F}` is unitary. The statement adds no stronger hypothesis.
2. **Rigidity: the supplied weak base change is the global base change.**
   `S` has the cuspidal weak base change `T`. So `S` is not isomorphic to
   `S ⊗ η`, because a self-twisted `S` has none (Arthur–Clozel III.4.2(b);
   Library `CyclicPrimeSelfTwistStatement`). By III.4.2(a) (Library
   `CyclicPrimeCuspidalLiftStatement`), `S` has a unique cuspidal weak base
   change `Π`, which is Galois-stable. By strong multiplicity one, as in
   Arthur–Clozel III.(2.4) (Jacquet–Shalika, Library C2,
   `CuspidalSpectralRigidityStatement`), `T` is identified with `Π`.
   Strong lifting is proved for Arthur and Clozel's `Π`, not for an
   arbitrary class with the same unramified parameters, so this
   identification is needed.
3. **Strong lifting at the unique place.** Arthur–Clozel III.5.1: a weak
   lifting between representations induced from cuspidal data is a strong
   lifting (Definition III.1.2). At every place `w'` above `v'`, the
   component `Π_{w'}` is the local base-change lift of `π_{v'}`. Since `w` is
   the only place above `v`, its decomposition group is all of `Gal(E/F)`.
   So `E_w/F_v` is cyclic of degree `ℓ`, unramified or totally ramified, and
   `T_w` is the base-change lift of `S_v` along `E_w/F_v`, not a component of
   a split product. The local components of a cuspidal representation are
   generic, but they need not be tempered. The lift is therefore the one of
   Chapter I, Section 6, extended by the Langlands classification after
   Proposition I.6.8. III.5.1 itself uses this extension: its proof invokes
   the Langlands classification for σ-stable representations.
4. **Local descent of supercuspidality.** Let `M/L` be cyclic of prime degree
   and `π` irreducible with supercuspidal lift `Π`. Realize `π` as the
   Langlands quotient of a representation induced from essentially tempered
   data. Those data are induced from generalized Steinberg representations
   `St(ω_i, a_i)` with `ω_i` supercuspidal. By Lemma I.6.10 each `ω_i`
   lifts either to a supercuspidal `Ω_i` or to `T_i × T_i^σ × ⋯ × T_i^{σ^{ℓ-1}}`
   with `T_i` supercuspidal and not σ-stable. Lemma I.6.12 lifts
   `St(ω_i, a_i)` to `St(Ω_i, a_i)` or to the corresponding product of
   `St(T_i^{σ^j}, a_i)`. By the extension after I.6.8, the lift of `π` is the
   Langlands quotient of the induced lift of the data. So the supercuspidal
   support of `Π` is the union, up to unramified twists, of the supports of
   these lifts. If `Π` is supercuspidal, its support has one element of full
   rank. Then there is exactly one block, with `a_1 = 1` and `ω_1` of full
   rank lifting to a supercuspidal representation, so `π ≅ ω_1` is
   supercuspidal. Plan Section 4.8 states this local argument, also for orbit
   sums. Only the supercuspidal case is used here.
5. **Actual components.** The proof must identify the supercuspidal factor
   of the supplied `P` at `w` with the irreducible local component `T_w` of
   the cuspidal realization `T`. It must then produce, at universe `uV`, an
   actual spectral presentation of `S` whose local component at `v` is the
   irreducible component `S_v`. Only then is the local conclusion of
   obligation 4 a witness of `HasSupercuspidalComponent`.

The local maps `Ch_{M/L}` of interface E2 may enter this proof, in the form of
the plan's E2 clause beyond supercuspidal classes. They are never premises of
the statement. The statement has no local-map parameter.

## 5. Relation to other Library statements

- **B4**, `CyclicWeakInductionSupercuspidalStatement`, concerns weak
  *induction* from `E` to `F` and needs distinct local Galois conjugates. B5
  concerns *descent* from a cuspidal weak *base change*. It needs no
  conjugates, no generator `σ` and no character `η`, and it neither replaces
  nor restates B4. B4 and its totally complex form remain unchanged in their
  own modules.
- **B1**, `CyclicStableDescentStatement`, produces the descents considered in
  the singleton branch. B5 is the premise that gives such a descent a
  supercuspidal component at the auxiliary place (plan Section 4.8).
- **B6**, the tower statement (the modules
  `Langlands.Automorphic.Unramified.PrimeCyclicBaseChangeTower` and
  `Langlands.Automorphic.Unramified.HeckeFamilyEndpoint` supply its tower and
  Hecke vocabulary), and **B7**, the archimedean statement, are separate interfaces.
  Neither is used here.

## 6. Sources and provenance

Provenance: *derived*. The statement is the global consequence, at one
non-split place, of the sources below, with the obligations of Section 4
retained. The sources give the statement and its eventual derivation. They
are not proof evidence.

- `operator-external-inputs-plan-2026-11-16`: operator note *Formalizing the
  large external inputs of the local Langlands correspondence for `GL_n`*,
  16 November 2026 (`external-inputs-plan.tex`). Section 2.2, item B5 (the
  statement, "from Arthur–Clozel III.5.1 and I.6"). Section 4.6, Interface
  (B5 follows from III.5.1 at one place together with E2 for the components of
  unitary cuspidal classes). Section 4.8, singleton case, Remark 4.2 with its
  local statement and item (3), and the comparison with the Library's
  branch statements.
- `arthur-clozel-1989-base-change`: J. Arthur and L. Clozel, *Simple Algebras,
  Base Change, and the Advanced Theory of the Trace Formula*, Annals of
  Mathematics Studies 120 (1989). Registered PDF pages are one-based and equal
  printed page + 14:
  - Chapter III, Definitions 1.1 and 1.2 (weak and strong base change),
    printed p.199 (PDF 213);
  - Chapter III, (2.4), printed p.200 (PDF 214);
  - Chapter III, Definition 4.1 and Theorem 4.2, printed p.202 (PDF 216);
  - Chapter III, Theorem 5.1 (strong lifting), printed pp.212–213
    (PDF 226–227);
  - Chapter I, Section 6: the extension of the lift to all irreducible
    representations by the Langlands classification after Proposition 6.8,
    printed pp.59–60 (PDF 73–74); Lemma 6.10, printed p.62 (PDF 76);
    Lemma 6.12, printed p.66 (PDF 80).

No source-specific errata file exists in the Library under either source ID.
The statement adds no `n < p` condition and makes no claim at places where
`v` splits in `E`.
