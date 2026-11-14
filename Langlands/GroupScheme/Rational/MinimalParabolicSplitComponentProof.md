# Minimal parabolics and their specified split components

Author: Worker 712.

The theorem
`Langlands.GroupScheme.minimalParabolicSplitComponent`, with universe parameter
`u`, in module
`Langlands.GroupScheme.Rational.MinimalParabolicSplitComponentProof` proves
exactly `Langlands.GroupScheme.MinimalParabolicSplitComponentStatement.{u}`.
It assumes no additional statement as a premise.
The theorem's axiom inspection reports only `propext`, `Classical.choice`,
and `Quot.sound`.

For every field `k`, connected reductive group scheme `G`, rational parabolic
`j : P ⟶ G`, supplied geometric solvable radical `r : R ⟶ P`, and maximal
split torus `a : A.toGrp ⟶ R`, it proves

```text
IsMinimalParabolicSubgroup j ↔ IsMaximalSplitTorus (a ≫ r ≫ j).
```

Here a split component of the possibly non-reductive parabolic means a maximal
split torus of its radical, as in the target. The radical is supplied, rather
than constructed. The field may be imperfect and has arbitrary characteristic.
All subgroup-functor comparisons are on every test scheme over `k`.

## Implemented proof

First the proof constructs a Levi adapted to the specified map `a`. Closedness
of `j` and `r` gives affineness of `P` and `R` from affineness of `G`.
The radical is smooth, hence locally of finite type.
`exists_maximalTorus_extension_of_finiteType` extends `a` to a maximal
absolute torus `s : S.toGrp ⟶ R`, with a map `f : A.toGrp ⟶ S.toGrp`
satisfying `f ≫ s = a`. The published
`parabolicRadicalTorusCentralizerLevi` supplies a rational Levi
`l : L ⟶ P` whose ambient inclusion represents `torusCentralizer (s ≫ r ≫ j)`.
The canonical `torusCentralizerFactor` gives a map `sL : S.toGrp ⟶ L`.
Set `aL = f ≫ sL`. The factorization equation and cancellation of the
closed embedding `j` give `aL ≫ l = a ≫ r`.

The published
`IsRationalLeviSubgroup.isCentral_of_factor_solvableRadical` makes `aL`
central in `L`. It is closed because its composite with the closed map `l`
equals the closed composite `a ≫ r`. It is therefore a central split torus.
For any central split extension `b : B.toGrp ⟶ L` and
`g : A.toGrp ⟶ B.toGrp` with `g ≫ b = aL`,
`IsRationalLeviSubgroup.centralTorusRadicalFactor` gives a closed map
`bR : B.toGrp ⟶ R` with `bR ≫ r = b ≫ l`. Cancellation of `r` gives
`g ≫ bR = a`. Maximality of `a` in `R` makes `g` an isomorphism.
This proves `IsSplitComponent aL`, the central split component predicate
inside the reductive Levi.

The published `parabolicDynamic` supplies a cocharacter `χ` whose dynamic
parabolic is represented by the original `j`. If `j` is minimal, the theorem
`IsRationalLeviSubgroup.isMaximalSplitTorus_splitComponent_of_dynamicMinimalParabolic`
applies to this presentation and `aL`. It proves ambient maximality of
`aL ≫ l ≫ j`, which equals the required map `a ≫ r ≫ j`.

Conversely, assume the required ambient maximality.
`IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic`
gives a cocharacter `ν` of `A` presenting this same parabolic, with

```text
Dynamic.centralizer (groupHom ν ≫ aL ≫ l ≫ j) = range (l ≫ j),
torusCentralizer (aL ≫ l ≫ j) = range (l ≫ j).
```

Their equality implies genericity by
`RationalCocharacter.isGenericCocharacter_of_centralizer_eq_torusCentralizer`.
Its affine and local finite type hypotheses follow from connected
reductivity of `G`. The published `genericMinimalParabolic` then makes
the presented dynamic parabolic a minimal rational parabolic functor.
Its equality with `range j` gives minimality of the original subgroup `j`
by the definitions.

## Provenance and scope

This is an internally derived composite proof from the published Library
results named above. The source attribution of the unchanged target is
Renard V.3.2, with the split-component convention of V.2.1; see
[the statement Markdown](ParabolicSplitComponentStatements.md) for its
original-source reading record. This proof adds no external assertion and
claims no new reading of the original literature.

The principal imported proof routes are documented in
[ParabolicRadicalTorusCentralizerLeviProof](ParabolicRadicalTorusCentralizerLeviProof.md),
[LeviRadicalCentrality](LeviRadicalCentrality.md),
[CentralLeviTorusRadical](CentralLeviTorusRadical.md),
[MinimalParabolicCompatibleRefinement](MinimalParabolicCompatibleRefinement.md),
[OriginalLeviCocharacter](OriginalLeviCocharacter.md),
[RationalCocharacterRealization](RationalCocharacterRealization.md), and
[GenericMinimalParabolicProof](GenericMinimalParabolicProof.md).
The construction only needs the absolute-torus centralizer Levi before
establishing `IsSplitComponent aL`; the whole split-component centralizer
equality used later comes from the published presenting-cocharacter theorem.
No sibling split-component statement is assumed. The other four individual
statements and their conjunction in the target module are outside this proof.
