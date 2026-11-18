# Complex-place parameters and distinct Mackey components in Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterData`,
namespace `Langlands.Global.Harris.Proposition48Problem`.

The module declares `universe uF uV` and sets `autoImplicit false`. Here and
below `r : ℕ` indexes `GL_(r+1)`. `Q : Proposition48Problem.{uF}` contains the
number fields `Q.E`, `Q.E'`, `Q.L` in `Type`; `uF` is the problem's local-field
universe. `IsInducedComplexPlaceParameter` and
`HasInducedComplexPlaceParameters` have universe `uF` alone.
`HasParameterSolution`, `IsMackeyConstituent` and
`HasDistinctMackeyComponents` have universes `.{uF, uV}` because they also use
the published solution or weak-induction relations with spectral-presentation
universe `uV`.

Definitions for the exact-stabilizer form of the induction for Harris 1998,
Proposition 4.8 (printed p.201). In that form the auxiliary character satisfies
Harris's condition (4.12) (proof of Lemma 4.7, printed p.204) instead of being
in general position. The problems are the published
`Proposition48Problem`, and the exact-stabilizer validity predicates are those
of the published `HarrisProposition48ExactStabilizerData`. The restated
proposition `Proposition48ExactStabilizerStatement` (Task 7413) is neither
imported nor used here. This module only defines
predicates. It asserts no existence, distinctness or compatibility.

## Why solutions carry parameters

The published branch statements demand regular algebraicity of the output,
but their premises do not explicitly relate archimedean components across
the cyclic step. The R2 design keeps track of the Langlands parameters at the
complex places: the intended output of each step has, at every complex place
`v` of `E`, the parameters of the representation induced from `ξ`. The later
proofs must read regular algebraicity off these parameters through the
archimedean bridge `CuspidalComplexParameterBridgeTCStatement` (stated
separately by Task 7463), using the published regularity of `ξ`. The induced
class gets its parameters from those of the children by the restricted
complex-place compatibility of cyclic base change and induction,
`RestrictedCyclicWeakBaseChangeComplexPlaceStatement` (restricted B7, stated
separately by Task 7552). Neither is imported by this module; the sibling
branch module takes both as named premises. This design is the
project operator's R2 choice for the exact-stabilizer branches. Restricted
B7(2) supplies parameters in the prime branch, and restricted B7(1) in the
singleton branch. B7(3), the whole-tower parameter transports and an endpoint
statement beyond rank one are not branch premises. Canonical B7 (Task 7479)
is a separate statement, not used here. Parameters are lists of
`ComplexCharacterData` compared up to order (`List.Perm`), because the
parameter of an isobaric sum has no preferred order of its blocks.

## Definitions

- `IsInducedComplexPlaceParameter Q v ds` for a complex place `v` of `Q.E`
  and `ds : List ComplexCharacterData`: there are `d : ℕ`, an enumeration
  `e : Fin d ≃ InfinitePlacesAbove Q.E' v.1` of the places of `E'` above `v`,
  and for each such place `w` an actual parameter `dξ w` of `ξ` at
  `complexPlaceAbove v w` (`HeckeCharacter.HasComplexPlaceParameter`), such
  that `ds` is a permutation of
  `complexPlaceLanglandsSum v e (fun w => [dξ w])`. That sum concatenates the
  one-block lists `[dξ w]`, each read in the coordinates of `v`
  (`complexPlaceParameterTransport`: unchanged if the embeddings agree,
  conjugated otherwise), in the order of `e`. This is the expected parameter
  at `v` of an automorphic induction of `ξ` from `E'` to `E`: the sum, over the
  places `w` of `E'` above `v`, of the characters `ξ_w`.
- `HasInducedComplexPlaceParameters Q c` for a cuspidal class
  `c : CuspidalOperatorRealization.IsoClass Q.E r`: at every complex place
  `v` of `Q.E` there is a list `ds` with `c.HasComplexPlaceParameter v ds`
  and `Q.IsInducedComplexPlaceParameter v ds`.
- `HasParameterSolution.{uF, uV} Q`: there are `r` and a cuspidal class `c`
  of `GL_{r+1}` over `Q.E` with `Q.IsSolution.{uF, uV} c` (weak induction of
  `ξ`, regular algebraic, conjugate self-dual, supercuspidal at `Q.Ps.v`) and
  `Q.HasInducedComplexPlaceParameters c`. It implies the published
  `Q.HasSolution.{uF, uV}`.
- `IsMackeyConstituent.{uF, uV} Q D a c` for an intermediate field `D` of
  `L/E`, `a : Q.L ≃ₐ[Q.E] Q.L` and a cuspidal class `c` over `D` (with
  `[CompactSpace (AdeleQuotient D)]`): `c` is a weak automorphic induction
  (`IsWeakAutomorphicInductionOf.{0, 0, uV}`) of the published Mackey
  character `Q.mackeyCharacter D a = a(ξ) ∘ N` of `Q.mackeyField D a = D · a(E')`,
  with `D · a(E')` a `D`-algebra by inclusion, as in `Q.mackeyRank`.
- `HasDistinctMackeyComponents.{uF, uV} Q D`: with the compactness instance
  `compactSpace_adeleQuotient D`, for all `a a' : Q.L ≃ₐ[Q.E] Q.L` whose
  classes in `Gal(L/D) \ Gal(L/E) / Gal(L/E')` (`DoubleCoset.mk` with the
  subgroups of `Q.MackeyIndex D`) are different, all `r`, and all cuspidal
  realizations `T U : CuspidalOperatorRealization D r` with unitary central
  characters such that `T.isoClass` is a Mackey constituent for `a` and
  `U.isoClass` one for `a'`: for every finite place `w` of `D` above
  `Q.Ps.v` and all spectral presentations `P` of `T` and `P'` of `U`
  (universes `.{0, uV}`), the local components `P.localComponent w.1` and
  `P'.localComponent w.1` are not isomorphic.

For clarity, the exact source-level binders and bodies of all five predicates
are reproduced below. There are no additional implicit parameters; `{r : ℕ}`
is implicit in the two class predicates where it occurs.

```lean
def IsInducedComplexPlaceParameter (Q : Proposition48Problem.{uF})
    (v : {v : InfinitePlace Q.E // v.IsComplex}) (ds : List ComplexCharacterData) :
    Prop :=
  ∃ (d : ℕ) (e : Fin d ≃ InfinitePlacesAbove Q.E' v.1)
    (dξ : InfinitePlacesAbove Q.E' v.1 → ComplexCharacterData),
    (∀ w, Q.ξ.HasComplexPlaceParameter (complexPlaceAbove v w) (dξ w)) ∧
      ds.Perm (complexPlaceLanglandsSum v e fun w => [dξ w])

def HasInducedComplexPlaceParameters (Q : Proposition48Problem.{uF}) {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass Q.E r) : Prop :=
  ∀ v : {v : InfinitePlace Q.E // v.IsComplex},
    ∃ ds : List ComplexCharacterData,
      c.HasComplexPlaceParameter v ds ∧ Q.IsInducedComplexPlaceParameter v ds

def HasParameterSolution (Q : Proposition48Problem.{uF}) : Prop :=
  ∃ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r),
    Q.IsSolution.{uF, uV} c ∧ Q.HasInducedComplexPlaceParameters c

def IsMackeyConstituent (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) (a : Q.L ≃ₐ[Q.E] Q.L)
    [CompactSpace (AdeleQuotient D)] {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass D r) : Prop :=
  letI : Algebra D (Q.mackeyField D a) :=
    (IntermediateField.inclusion (show D ≤ Q.mackeyField D a from le_sup_left)).toAlgebra
  c.IsWeakAutomorphicInductionOf.{0, 0, uV} (Q.mackeyCharacter D a)

def HasDistinctMackeyComponents (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) : Prop :=
  letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
  ∀ a a' : Q.L ≃ₐ[Q.E] Q.L,
    DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup a ≠
      DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup a' →
    ∀ (r : ℕ) (T U : CuspidalOperatorRealization D r),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter U →
      Q.IsMackeyConstituent.{uF, uV} D a T.isoClass →
      Q.IsMackeyConstituent.{uF, uV} D a' U.isoClass →
      ∀ (w : FinitePlacesAbove D Q.Ps.v)
        (P : CuspidalSpectralPresentation.{0, uV} T)
        (P' : CuspidalSpectralPresentation.{0, uV} U),
        (P.localComponent w.1).isoClass ≠ (P'.localComponent w.1).isoClass
```

The class parameter relation is the published actual parameter predicate;
`HasInducedComplexPlaceParameters` does not replace it by a permutation
closure. The separate expected list is compared up to order in
`IsInducedComplexPlaceParameter`. The coordinates are those already fixed by
`HasComplexPlaceParameter` and `complexPlaceParameterTransport`, the same
coordinates as those of the bridge of Task 7463 and of its normalization module
`ComplexPlaceParameterWeights` (Task 7455), as point (a) of the R2 ruling
requires. This module introduces no different shift or embedding convention.

## Provenance

`HasDistinctMackeyComponents` is the property of the Mackey constituents that
the published prime branch obtains from the comparison at a split
supercuspidal place (`HarrisSupercuspidalLocalComparisonStatement`) and the
general position of the auxiliary character. Harris uses it in the
prime-orbit case of the proof of Proposition 4.8 (printed pp.202–203). Under
condition (4.12) it is the content of claim (2) of Remark 4.2 of the
operator's plan note (source `operator-external-inputs-plan-2026-11-16`,
`external-inputs-plan.tex`, Section 4.8, TeX lines 859–894, with the prime
branch at line 908). The sibling module
`HarrisProposition48ExactStabilizerDistinctnessStatement` states its
derivation from B6 as an unproved implication. The parameter predicates use the vocabulary of
`Langlands.Automorphic.IsobaricComplexPlaceParameter` and
`Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport`; their
normalization is that of `HasComplexPlaceParameter`.

These parameter predicates and the distinctness predicate are internal
interfaces of the R2 design, not definitions or statements of Harris. The
design sources are the operator plan, Section 2.2 (B5–B7, TeX lines 196–199)
and Section 4.8 (Remark 4.2 and the branch paragraphs, lines 859–912), and the
[operator's R2 ruling](/home/taskhub/pilot/correspondence/a79e2e832569567a8582b3c994f2fc1b.md),
answer to request `c292736a05f55d4fba67d1a01b7fb2e2`. The ruling requires the
bridge's parameter vocabulary and normalization and restricts B7(1)/(2) to
unitary cuspidal classes supercuspidal at the auxiliary conjugate pair,
without an algebraicity hypothesis.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210, source
`harris-1998-local-langlands`, Proposition 4.8 (p.201) and its proof
(pp.201–203), and condition (4.12) in the proof of Lemma 4.7 (p.204).

## Status

Definitions only. Nothing is proved in this module, and no published
declaration is changed.
