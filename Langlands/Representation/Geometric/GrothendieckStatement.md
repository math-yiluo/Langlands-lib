# The geometric lemma in exact finite-length K0

`Langlands.Geometric.GeometricLemmaGrothendieckStatement F T` states the
Grothendieck-class formula obtained from the existing actual normalized
geometric lemma. This module supplies a proposition definition and no proof.
It is an internal derived target for assembling the formal Aubert identities.

Fix a prime `p`, an actual field `F : PadicField.{uF} p`, and its supplied
compatible topological data `T`. For every positive rank `n` and ordered block
shapes `B C : BlockShape n`, the proposition asserts that there are source
refinements `S`, target refinements `R`, and all three actual intersection
subgroup equalities on each side, together with a finite enumeration
`e : Fin m ≃ MinimalRepresentatives B C`, such that every actual finite-length
smooth complex representation `A` of `B.Levi F.Carrier` satisfies

```text
r_C(i_B([A])) = sum_i [geometricPieceSmoothFunctor(e(i))(A)].
```

Here `i_B` and `r_C` are exactly the published `normalizedInductionK0` and
`normalizedJacquetK0`. Each acts on the Grothendieck group of actual smooth
representations of finite group-algebra length, quotiented by all actual
short exact sequences, including nonsplit ones. The displayed class equality
lies in the group for `C.Levi F.Carrier`. Finite length does not mean finite
complex vector-space dimension.

The refinements, subgroup equality witnesses and enumeration are selected
before quantifying over `A` and its finite-length proof. Thus a single choice
works for every input representation. The finite-length proofs of all
geometric pieces are existential conclusions for each input. No finite-length
assumption on the pieces, splitting, irreducibility, admissibility, central
character or theorem-valued geometric-lemma premise is added.

The smooth piece is the already-published
`CuspidalSupport.geometricPieceSmoothFunctor`: actual normalized refined
Jacquet restriction, relabeling along equality of the source intersection
Levi, inverse-conjugation intersection transport, relabeling along equality
of the target intersection Levi, and actual normalized refined induction.
Its published `geometricPieceSmoothFunctor_toRep` identifies its underlying
functor with `Geometric.geometricPieceFunctor`. The full intersection
equalities are conclusions even though the composite needs only their
Levi components.

The conventions are inherited from those actual functors: upper ordered block
parabolics, positive half-modulus covariance and right translation for
induction, and inverse half-modulus normalized coinvariants for Jacquet
restriction. There is no extra character or alternating coefficient in this
geometric-lemma formula.

The field and carrier universes are independent. The input and every output
use the saturated carrier universe `max uF uV`; applying induction again does
not enlarge this universe. The group universe remains `uF`. Rank zero is
outside this target because the published actual geometric lemma has a
positive-rank hypothesis. Future identities quantified over all ranks must
handle zero separately. An empty enumeration is permitted by the syntax;
its equivalence with all minimal representatives constrains when it can occur.

## Internal provenance and remaining proof

This target is derived from the existing
`Geometric.PadicGeometricLemmaTheorem`, whose actual proof is
`Geometric.padicGeometricLemma`, and the published finite-length preservation
and class formulas for normalized induction and Jacquet restriction. It is
not a new transcription of an original-literature assertion. The source
correspondence for the actual geometric lemma remains in its existing
statement and proof Markdown.

The intended derivation takes the uniform witnesses and natural filtration
from `padicGeometricLemma` at the saturated carrier universe. Forgetting the
smooth piece functors gives exactly the functors in that filtration. Actual
normalized induction followed by Jacquet restriction preserves finite length.
The adjacent short exact sequences in the filtration therefore give finite
length of the pieces and their class sum by telescoping in exact K0.
The two named K0 generator formulas identify the left side of that sum with
`r_C(i_B([A]))`. This paragraph specifies a proof route; this file implements
none of it.

The proposition does not state a natural splitting or a particular canonical
choice of refinements. It does not prove induction commutation, involutivity,
irreducibility of an Aubert image, or either direction of the analytic segment
classification.
