# Closed-ideal descent for iterated Laurent covers and all-unit standard covers

This is an internal prerequisite for finite-cover closed-ideal descent. It
proves `IdealCoverDescent` for two families of rational data over a presented
strict affinoid algebra `P`: the finite iterated unit-radius Laurent covers, and
the standard rational cover of a tuple of units. The motivating source is
Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Kiehl's Theorem and Remark 1.2.1(ii), printed p.15 / PDF p.12, registered as
`berkovich-1993-etale-cohomology`. The reduction is internal. It has the same
shape as the Library's scalar proofs `IteratedLaurentScalarDescentProof` and
`AllUnitStandardRationalGluingProof`, here applied to ideals, and transcribes
no proof from the source.

Throughout, `K` is a complete ultrametric normed field and every theorem
assumes `hK : ∃ c : K, 1 < ‖c‖`. For a family `D` of rational data over `P`,
`IdealCoverDescent D` says: for every family of ideals `I i` of the algebras of
`D i` whose closed extensions to every actual pairwise intersection agree, each
`I i` is the closed extension along the base map of `D i` of the ideal of
elements of `P` whose image lies in every `I j`.

## The branch inclusion

`RationalData.iteratedLaurentBranchInclusion g b η`, for `g : Fin (m + 1) → P`,
`b : Bool` and `η : Fin m → Bool`, is a morphism of rational data over the
algebra of `laurentChoice (g 0) b` (the upper piece `|g 0| ≤ 1` for `false`,
the lower piece `|g 0| ≥ 1` for `true`). Its source is the leaf `η` of the
iterated Laurent cover of the images of `g 1, …, g m` in that algebra. Its
target is the pullback of the full leaf `Fin.cons b η` of the cover given by
`g`. The definition is the inverse of the Library's
`iteratedLaurentBranchIso g (Fin.cons b η)`.

## Binary Laurent descent in existence form

`binaryIdealDescent_laurent hK f` states `BinaryIdealDescent (laurentUpper f)
(laurentLower f)`: an ideal of the upper algebra and an ideal of the lower
algebra with equal closed extensions to their actual intersection are the
closed extensions of one ideal of `P`. The proof takes the ideal
`laurent_closedIdealMap_inf_comap_eq` provides, the ideal of elements whose
two images lie in the two given ideals.

## Iterated Laurent covers

`idealCoverDescent_iteratedLaurent hK m` states that for every `P` and every
`g : Fin m → P`, the family `ε ↦ iteratedLaurent g ε` indexed by
`ε : Fin m → Bool` satisfies `IdealCoverDescent`. The proof is by induction on
`m`, for all `P` at once.

- `m = 0`, in a private lemma: the only leaf is `whole K P`. Applying
  `wholeEvaluation K P` and then the base map of `whole K P` is the identity of
  its algebra (`wholeBaseMap_comp_evaluation`). Let `I` be the ideal on
  the only leaf, and `J` the ideal of elements of `P` whose image lies in `I`.
  The closed extension of `J` is contained in `I`, because `I` is closed by
  `PresentedStrictAffinoidAlgebra.isClosed_ideal`. Conversely, every `s ∈ I` is
  the image of `wholeEvaluation K P s`, which lies in `J`, so `s` lies in the
  closed extension.
- `m + 1`: apply the Library's `laurentSplitIdealDescent` with the function
  `g 0`, the point cover `iteratedLaurent_covers g`, and
  `binaryIdealDescent_laurent hK (g 0)`. For each branch `b`, it remains to show
  descent for the family of pullbacks of the leaves of `g` to the algebra of
  `laurentChoice (g 0) b`. This follows from
  `IdealCoverDescent.of_refinement`. The finer family is the iterated Laurent
  cover of the `m` images of `g 1, …, g m` in that algebra, which covers its
  spectrum by `iteratedLaurent_covers` and satisfies descent by the induction
  hypothesis. Its leaf `η` maps to the index `Fin.cons b η` along
  `iteratedLaurentBranchInclusion g b η`.

The induction never needs descent for a product cover: only the leaves with
first choice `b` are used to refine the pullback to branch `b`.

## All-unit standard covers

`idealCoverDescent_allUnitStandardRational hK f hf hu`, for `f : Fin n → P`
with no common zero on the Banach spectrum (`hf`) and all entries units
(`hu`), states `IdealCoverDescent (standardRational f hf)`.

- If `n = 0` the index type is empty and the statement holds vacuously.
- If `n > 0`, apply `IdealCoverDescent.of_refinement` with the iterated
  Laurent cover of the `n * n` ratios `allUnitRatios f`, which satisfies
  descent by the previous theorem and covers the spectrum by
  `iteratedLaurent_covers`. Leaf `ε` maps to index `allUnitLaurentIndex ⟨ε, hn⟩`
  along the Library's inclusion `allUnitLaurentInclusion f hf hu ⟨ε, hn⟩`.

## Scope

The results hold over nontrivially normed `K`, for arbitrary `P`, arbitrary
tuples `g`, and, for the all-unit theorem, any tuple of units without a common
zero. Nothing is assumed about reducedness or a nonempty spectrum. The module
does not treat standard covers with non-unit entries, does not prove the
finite-cover `IdealEffectivenessStatement`, and changes no Library file.
