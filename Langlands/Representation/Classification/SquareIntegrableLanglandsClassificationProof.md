# Square-integrable Langlands quotient classification

Author: Worker 596.

`Langlands.Classification.squareIntegrableLanglandsClassification.{uF,uV}`
proves exactly the published proposition
`Langlands.Classification.SquareIntegrableLanglandsClassification.{uF,uV} F T`.
Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
It adds no premise.

The proof supplies all four inputs to the published
`squareIntegrableLanglandsClassification_of_regular` reduction with
unconditional published theorems:

- `squareIntegrableEqualExponentGrouping.{uF,uV} F T`;
- `temperedBlockUniqueness.{uF,uV} F T`;
- `Langlands.glRegularLanglandsHeadExistence.{uF,uV}`;
- `Langlands.glRegularLanglandsDataUniqueness.{uF,uV}`.

The last theorem combines the proved ordered parameter comparison, actual
fixed-parameter tensor recovery and algebraic factor recovery. Its hypotheses
remain arbitrary irreducible quotient maps. Each input is imported by Lean
module name from the published Library.

All data and representation carriers have universe `max uF uV`, with
independent `uF` and `uV`. Every result retains the original supplied
`F.TopologicalData`, positive rank, weakly decreasing unitary exponents and
actual normalized upper-parabolic induction.
The conclusion is precisely an equivalence between isomorphism of arbitrary
irreducible quotients and a finite occurrence bijection matching actual blocks
after the displayed rank transport. No chosen forms, unitary-exponent witnesses
or datum records are compared.

## Supporting consequences

`squareIntegrableLanglandsHeadExistence` proves the existing proposition of
that name. Grouping constructs a regular tempered datum `t` and an actual
isomorphism `d.induced ≅ t.standardModule`. The regular head theorem supplies
an irreducible head of the latter. `IsIrreducibleHead.of_equiv` transports it
back through the inverse source equivalence. This transports both the actual
surjective intertwiner and the universal equality of kernels, including maps
to isomorphic irreducible targets.

`squareIntegrableLanglandsQuotientUniqueness` proves its existing proposition.
The preceding head theorem and the published
`nonempty_iso_of_isIrreducibleHead` identify arbitrary irreducible quotients of
the same source. The helper constructs the equivalences using the common head
kernel; the original quotient witnesses are not strengthened.

`nonempty_iso_of_squareIntegrableLanglands_blockMatching` proves the reverse
implication of the final target without any remaining hypothesis. It
specializes the published `nonempty_iso_of_rankIso` to the three closed inputs
above. The supplied finite equivalence retains repeated blocks, and each
block comparison uses exactly the target's rank equality transport. The
reduction proves equality of matched unitary exponents using the actual
unitary central characters at a scalar uniformizer. It identifies equal
exponent groups, applies tempered block uniqueness to the normalized blocks,
identifies the regular standard modules, and applies regular head uniqueness.
It never compares chosen forms or exponent witnesses as datum structures.

## Classification proof

The final theorem invokes
`squareIntegrableLanglandsClassification_of_regular` with the four closed
proofs above. Its forward direction
groups each datum, transports the given arbitrary quotient maps, and applies
regular data uniqueness to the isomorphic quotients. That matches the groups
by an order isomorphism, equal ranks, equal exponents and actual block
isomorphisms. Tempered block uniqueness matches all normalized blocks within
each group. Equality of the group exponents untwists them, and
`Equiv.ofFiberEquiv` assembles the finite occurrence bijections. This is exactly
the target's permutation and rank-transported block-isomorphism conclusion.

The reverse direction is the argument of
`nonempty_iso_of_squareIntegrableLanglands_blockMatching` described above:
matching actual blocks forces equal exponents, identifies their grouped
standard modules, and regular head uniqueness compares the given weak
quotients. Repeated blocks remain separate occurrences throughout the finite
bijections.

## Original sources and proof boundaries

Henniart, *Une caractérisation de la correspondance de Langlands locale pour
GL(n)* (2002), §2.8, printed p.596, states the weakly decreasing
square-integrable-block head theorem, ordering independence and classification
by the nonzero free commutative monoid on essentially square-integrable
classes. Sections 2.5–2.6, printed pp.594–595, fix the normalized upper
induction and individual special-block conventions. These original pages
were read for this proof.

Rodier, *Représentations de GL(n,k) où k est un corps p-adique* (1982),
§4.3, Theorem 3(a–c), printed pp.211–212, states the segment-head quotient
classification. Its subsequent explanation invokes Propositions 11–13 and
the Langlands quotient theorem. Proposition 11 explicitly refers to an
unpublished result of Bernstein. This passage does not constitute an
independent proof of all its inputs. It was read in full, and the printed
p.212 was checked as an image.

The implemented route instead uses the published regular-tempered reduction
and its proved inputs. Kudla, *The local Langlands correspondence: the
non-archimedean case* (1994), §2.2, Proposition 2.2.1,
equations (2.2.2)–(2.2.3) and Theorem 2.2.2, printed pp.372–374, describe
square-integrable induction, equal-exponent grouping and regular tempered
data uniqueness. Those pages were read. The finite fibers and explicit
rank transports are internal bookkeeping explained in the imported proof
Markdown. This module is a derived assembly of the four proved inputs; their
paired Markdown records the analytic and algebraic routes establishing them.

The published note `notes/jacquet/silberger-lemma53-scope.md` was read.
The head-existence dependency uses the supported relative comparison,
including the constituent restriction required by that note. The current
assembly introduces no unrestricted use of Silberger's printed Lemma 5.3.
It uses neither Zelevinsky §9.17 nor the final square-integrable
classification as an input.

Registered original sources:

| Source ID | Locator | SHA-256 |
| --- | --- | --- |
| `henniart-2002-characterization` | §§2.5–2.8, pp.594–596; PDF pp.8–10 | `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306` |
| `rodier-1982-gln` | §4.3, pp.211–212; PDF pp.12–13 | `389a9155f59022f5f5403bf568216f66b407b6d47e98221d115dcd85e076c8fc` |
| `kudla-1994-local-langlands-nonarchimedean` | §2.2, pp.372–374; whole-volume PDF pp.382–384 | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` |
