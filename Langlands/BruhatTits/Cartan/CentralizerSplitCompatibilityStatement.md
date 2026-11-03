# Statement targets for the split-torus consequence of full V6

This focused pair states the compatibility comparison needed to relate the
full centralizer axiom to the torus compatibility in `KPApartmentData`.
Both declarations are proposition definitions. Proofs are separate work.

## Sources and provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, Axiom 4.1.4(A1) and Remark
4.1.5, printed page 159 / PDF page 190, define centralizer translation as
the projection of the negative of the character valuation. Definition
6.1.2(V6), printed page 199 / PDF page 230, gives full centralizer
compatibility and then its consequence for points of the split torus.
The corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, PDF page 25, define the character
valuation with positive field order. The Chapter 4 and Chapter 6
corrections on PDF pages 27–29 and 32 leave these two axioms unchanged.
The additional corrected Chapter 7 hypothesis on PDF page 33 is not
provided by either statement here.

These targets are derived formulations of the displayed V6 consequence
using the Library's actual character restriction, normalized local-field
order and represented-centralizer datum. The explicit real-character
comparisons below remain premises. At the level of the two compatibility
predicates the implication makes sense for any root-function family; it
therefore also applies to a family already satisfying the separate
root-datum valuation axioms. No valuation axiom is inferred from an
arbitrary family.

## Actual objects and common hypotheses

`F` is any nonarchimedean local field with the existing field, valuation and
topology instances, with no restriction on its characteristic. `G` is an
actual connected reductive group scheme over `F`. Affineness of `G` is
also an explicit instance required by the imported root-group predicates.
The inclusion `i : S.toGrp ⟶ G` is an actual maximal split torus in the
sense of `IsMaximalSplitTorus`.

`C : CentralizerDatum i` consists of the actual group scheme `C.Z`, a
closed subgroup morphism `C.j : C.Z ⟶ G` representing the all-test-scheme
centralizer functor `torusCentralizer i`, and a morphism `C.s : S.toGrp ⟶ C.Z`
with `C.s ≫ C.j = i`. Its last field is the explicit hypothesis
`C.bijective : Function.Bijective (restrictionEvaluation C.s)`, needed to
define the existing real centralizer valuation. This datum does not assert
that the comparison is bijective for every actual centralizer; that is the
separate `CentralizerValuationComparisonStatement` target.

The family `φ : RootFunctionFamily S G` is required to satisfy
`IsCentralizerCompatible i C.j C.s C.bijective φ`. This is full V6 on the
actual centralizer points. It uses `rationalPoints.map C.j` for the
conjugation action and `centralizerTranslation C.s C.bijective` for its
translation. The target is exactly
`IsSplitTorusCompatible i (localFieldOrder F) φ`, the existing predicate
used for the torus part of V6 in `KPApartmentData`.

## General torus target

`CentralizerSplitCompatibilityStatement` quantifies over all the common
inputs just described. It also requires

```text
Function.Bijective (restrictionEvaluation (𝟙 S.toGrp)).
```

This identity-character comparison is retained explicitly. The statement
then concludes the torus compatibility for every full-V6-compatible
family. In pointwise notation its conclusion is

```text
φ_a(i(t)⁻¹ u i(t)) = φ_a(u) - ord(a(t))
```

for every actual relative root `a`, every `t ∈ S(F)` and every
`u ∈ U_a(F)`. In Lean the equality is in `WithTop ℝ`; the negative order
is cast into that type and added to `φ_a(u)`. No finiteness assumption on
an individual value of the family is made.

## Coordinate split-torus target

`CoordinateCentralizerSplitCompatibilityStatement` takes
`S = splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I`, for an
arbitrary finite type `I`, including the empty type. The inclusion `i`
is still required to be maximal, and `C` still represents its actual
centralizer. This target has the same full-V6 premise and conclusion,
but omits the identity-character comparison premise. Its intended
normalization uses the existing coordinate split-torus valuation. It does
not replace the general target by a split-group specialization: the
ambient connected reductive `G` is not required to be split or quasi-split.
The declaration of the coordinate target explicitly fixes this model for
`S`; neither target constructs a coordinate identification for an arbitrary
chosen split torus.

## Normalization and scope

`centralizerValuation C.s C.bijective` is positive: evaluation at a
restricted rational character is the real cast of that character's
normalized integer field order. `localFieldOrder F` is the same real cast
of `fieldOrderUnits F`. The translation used by V6 is its negative,
`centralizerTranslation = -centralizerValuation` in additive notation.
The factorization in `C` identifies `C.j(C.s(t))` with `i(t)` on actual
rational points. These conventions fix the sign in the displayed
split-torus consequence; the positive valuation is not used directly as
the apartment translation.

The targets assert compatibility implications under the listed premises.
They assert no existence of `C`, no automatic character-comparison
bijectivity, and no existence of a root-datum valuation, apartment or
corrected building. They do not supply V7, AS5, the full corrected
valid-building predicate or general building existence. In particular,
they do not justify applying a Cartan theorem to arbitrary
`KPApartmentData`. They define no `Z(F)^0` or parahoric `P_x`, and assert
no compactness, maximality, Cartan coverage, double-coset classification
or identification of a valuation image with the full cocharacter lattice.
