# Inertia surjectivity, finite presentations and conductor independence

Worker 60 authors this statement unit. Its declarations are `Prop`-valued
definitions in `Langlands.Ramification.Padic`. They state mathematical
obligations and do not prove them. All maps, presentations, pullbacks and
conductor expressions come from
`Langlands.LocalFactor.Ramification.InertiaPresentation`.

## Scope and actual objects

The prime `p` and finite p-adic field `F : PadicField.{uF} p` are arbitrary.
Finite extensions are actual
`FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)`
objects, with their inherited embeddings and canonical topological data.
No abstract quotient map replaces a field restriction.

The representation `A` is
`FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)`. Thus it is a
finite-dimensional complex action on its actual carrier, with carrier
universe `uV` independent of the field universe `uF`. The equivalence clause
uses another action `B` in independent universe `uW`. The scope includes
rank zero and does not impose irreducibility, semisimplicity, unitarity, or
finite image of the entire Weil group.

`A.IsContinuous` means continuity into the usual finite-dimensional complex
endomorphism topology. It is the hypothesis of the two continuous-action
clauses. The conductor clauses apply to any supplied genuine presentations,
even without a separate continuity hypothesis.

## Named clauses

1. `AbsoluteInertiaRestrictionSurjectivityStatement F` asserts, for every
   actual finite Galois subfield `L`, surjectivity of
   `absoluteInertiaRestriction F L` from the actual absolute inertia group
   onto the residue-kernel inertia of `L/F`.
2. `WeilInertiaRestrictionSurjectivityStatement F` asserts surjectivity of
   the specified `weilInertiaRestriction F L` for every such `L`.
3. `FiniteInertiaRestrictionSurjectivityStatement F` asserts surjectivity of
   `finiteInertiaRestriction F h` for every actual inclusion `h : L ≤ M`.
   These three clauses assume neither surjectivity nor upper-ramification
   quotient compatibility.
4. `ContinuousWeilFiniteInertiaImageStatement F A` states
   `A.IsContinuous → A.HasFiniteInertiaImage (localInertia F)`.
   Finite inertia image is a conclusion, not input data.
5. `ContinuousWeilFiniteInertiaPresentationStatement F A` states precisely
   `A.IsContinuous → Nonempty (FiniteInertiaPresentation F A)`. The
   presentation has only an actual extension `L` and the containment
   `ker(weilInertiaRestriction F L) ≤ ker(localInertiaRepresentation F A)`.
   Neither a presentation nor finite inertia image is assumed.
6. `FiniteInertiaConductorRefinementStatement F A` states that for any
   presentation `P`, containing actual field `M`, and inclusion proof
   `h : P.extension ≤ M`, both conductor expressions for `P.refine M h`
   equal those for `P`. Surjectivity proofs `hP` and `hM` for the specified
   Weil inertia restrictions are universally quantified to make the existing
   conductor expressions available.
7. `FiniteInertiaConductorCompositumStatement F A` uses exactly
   `R := FiniteInertiaCommonRefinement.compositum F A P Q`. Its field is
   `P.extension ⊔ Q.extension`. It asserts that the inertia Artin and Swan
   sums of `R.leftRepresentation hP` equal the corresponding expressions
   for `P`, and that the sums of `R.rightRepresentation hQ` equal those for
   `Q`. These are the published pullbacks along actual finite inertia
   restrictions. Only `hP` and `hQ` are needed to form the expressions;
   no common-field surjectivity or conductor equality is assumed.
8. `FiniteInertiaConductorIndependenceStatement F A` states equality of
   the Artin expressions and equality of the Swan expressions for arbitrary
   genuine presentations `P,Q` of the same `A`, with universally quantified
   surjectivity proofs for their actual Weil restriction maps.
9. `FiniteInertiaConductorEquivalenceStatement F A B` states these two
   equalities for arbitrary genuine presentations of two actions related by
   an actual `FiniteRepresentation.Equiv A B`. This is an invertible linear
   intertwiner of the full Weil actions, not an assumed equality of
   conductor values. The two carrier universes remain independent. Together
   with existence and universal surjectivity, this is the compatibility
   needed to define conductors on continuous representation isomorphism
   classes; this unit does not construct the quotient functions.

`InertiaSurjectivityPresentationAndConductorIndependenceStatement` is the
fully quantified conjunction of all nine clauses. It universally quantifies
the prime, its primality instance, the field, and the representation objects.
Its only universe parameters are `uF`, `uV`, and `uW`. There is no external
surjectivity assumption on the aggregate: surjectivity itself is a conjunct.
The explicit surjectivity proofs in clauses 6–9 are required arguments of
the existing expressions, and the universal surjectivity conjunct supplies
their intended arithmetic content.

The common-refinement record reused here stores only a finite field and
two actual inclusions. No new record is introduced, and no conductor
equality, ramification compatibility, or presentation-existence assertion
is hidden in its fields.

## Original sources and derived content

The following passages were read directly in the registered originals.
No source-specific errata notes were present in the consulted Library.

- Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay
  Greenberg, Springer GTM 67 (1979), source `serre-1979-local-fields`,
  retained at
  `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`,
  SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
  Chapter I, section 7, printed pages 20–23 (PDF pages 28–31), defines
  inertia as the residue-action kernel. Proposition 20 identifies the
  residue quotient, and Proposition 22(b), printed page 22 with proof on
  page 23, gives exactness of finite inertia restriction. This is the
  direct source for clause 3. The absolute version in clause 1 is the
  inverse-limit consequence, and clause 2 transports it through the actual
  Weil inertia projection; these are derived formulations of the arithmetic
  maps, not verbatim statements of Proposition 22.
- In the same source, Chapter IV, section 1, printed pages 61–62 (PDF pages
  68–69), identifies the zeroth lower ramification group with inertia.
  Section 3, printed pages 73–75 (PDF pages 80–82), gives the upper
  numbering, quotient compatibility (Proposition 14), and the inverse-limit
  formulation for infinite Galois extensions. These give the ramification
  context and route to conductor refinement, but no such compatibility
  proposition is an assumption in this unit.
- In the same source, Chapter VI, section 2, printed pages 99–102 (PDF pages
  106–109), gives the Artin character and conductor. Proposition 2 and
  Corollary 1' on pages 100–101 express the Artin conductor as the weighted
  sum of fixed-space codimensions. Proposition 3 and its corollary on page
  101 (PDF page 108) give invariance under quotient inflation. The
  inertia-only presentation comparisons here are derived applications of
  the ramification and conductor formalism, rather than a claim that Serre
  states these Lean presentation records. Swan invariance follows from
  Artin invariance and invariance of the inertia-fixed codimension.
- Pierre Deligne and Guy Henniart, *Sur la variation, par torsion, des
  constantes locales d'équations fonctionnelles de fonctions L*,
  Inventiones Mathematicae 64 (1981), 89–118, source
  `deligne-henniart-1981-variation`, retained at
  `/home/taskhub/central-library/Deligne-Henniart--Sur la variation, par torsion, des constantes locales d'equations fonctionnelles de fonctions L--1981.pdf`,
  SHA256 `54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.
  Section 0.5, printed page 92 (PDF page 4), specifies continuous
  finite-dimensional complex representations, asserts finite inertia
  action, and records the relation between Artin conductor, Swan conductor
  and inertia-fixed codimension. Clause 4 directly translates its finite
  inertia assertion. The preceding paragraph identifies Weil inertia with
  absolute inertia.

Clause 5 is an internal translation of finite continuous inertia action
into the existing exact kernel presentation. Its mathematical route uses
the open kernel of the finite continuous inertia action and the finite
Galois restriction neighborhoods of the identity: choose a finite Galois
subextension whose inertia restriction kernel lies in the action kernel.
Finite image alone is not substituted for this containment, and the exact
containment is not attributed verbatim to Deligne–Henniart.

Clauses 6–9 translate conductor invariance to these actual presentations.
The already available `representation_refine` identifies refined descent
with the actual pullback, and `FiniteInertiaCommonRefinement.representations_eq`
identifies the two pullbacks on the actual compositum given its separately
supplied surjectivity. The remaining conductor-sum comparison is the
arithmetic assertion being stated. The equivalence variant uses invariance
of fixed-space dimensions under invertible intertwiners and the same
common-field comparison. These observations explain provenance and a
possible proof route; they are not proofs supplied by this statement unit.

## Boundary with other statements

This unit concerns actions of finite **inertia** groups obtained from
continuous Weil actions. It does not require the full Weil action to factor
through a finite Galois group.
`FiniteGaloisConductorInflationAndIndependenceStatement` concerns full finite
Galois representations and is a distinct target; it is not restated here.
The Herbrand and absolute ramification arithmetic statement units likewise
remain separate. No elementary construction proofs from
`InertiaPresentation` are repeated, and no proof of any new clause is
claimed. Independent semantic review and Library publication are separate
from compiling these proposition definitions.
