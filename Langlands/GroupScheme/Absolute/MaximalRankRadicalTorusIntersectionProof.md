# Radical intersections in connected subgroups of maximal rank

Worker 950 and Worker 1496.

`Langlands.GroupScheme.maximalRankRadicalTorusIntersection` proves the
published proposition
`Langlands.GroupScheme.MaximalRankRadicalTorusIntersectionStatement.{u}` for an
arbitrary universe `u`, with no additional premise.

Let `k : Type u` be an algebraically closed field, `G` a connected reductive
group over `Spec k`, and `j : H ⟶ G` a smooth connected closed subgroup. Let
`t : T ⟶ G` be a maximal torus with a factor `f : T ⟶ H` such that
`f ≫ j = t`, and let `r : R ⟶ H` satisfy `IsSolvableRadical r`. The
conclusion is a commutative group scheme `S`, a closed map `sT : S ⟶ T` and a
maximal torus `sR : S ⟶ R` with

```text
sT ≫ f = sR ≫ r,
range (sT ≫ f) = range f ∩ range r,
```

where the range equality is between subgroup functors, on every scheme over
`Spec k`. The exact encoding is described in
[the target statement](MaximalRankRadicalTorusIntersectionStatement.md).

## Implemented proof

The proof is one application of the published theorem
`maximalRankRadicalTorusIntersectionStatement_of_solvableTorusQuotient` from
[`MaximalRankRadicalTorusIntersectionOfQuotient`](MaximalRankRadicalTorusIntersectionOfQuotient.md),
of type

```text
SolvableTorusQuotientStatement.{u} → MaximalRankRadicalTorusIntersectionStatement.{u}.
```

Its premise is supplied by the published theorem
`solvableTorusQuotient : SolvableTorusQuotientStatement.{u}` in
[`SolvableTorusQuotientProof`](SolvableTorusQuotientProof.md), at the same
universe. So the resulting theorem has exactly the target type.

The reduction works inside the smooth connected solvable fppf product
`P = range r · range f` of `H`. There, maximal tori are conjugate, by
`maximalToriAreConjugate_of_solvableTorusQuotient`, and `R` is the
semidirect product of its unipotent part and any maximal torus, by
`solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient`. Both use
the premise together with the published split-extension proof. The Library
theorem `exists_radicalTorusIntersection_of_complement` applied in `P` gives
`S`, `sT` and `sR`. The range equality is then transported back to `H` along
the closed immersion `P ⟶ H`. The details are in the Markdown of that module.

The axioms are `propext`, `Classical.choice` and `Quot.sound`. The proof
does not assume `MaximalTorusConjugacyStatement`, `BorelConjugacyStatement`,
any rational Levi statement or the two-parabolic consumer theorem.

## Companion module

The same candidate adds
[`SolvableMaximalTorusSemidirectProof`](SolvableMaximalTorusSemidirectProof.md).
Its theorem `solvableMaximalTorusSemidirect` proves
`SolvableMaximalTorusSemidirectStatement.{u}` (Milne 2017, Theorem 16.33(d))
with no premise, by applying the same conditional reduction to
`solvableTorusQuotient` and `solvableSplitExtension`. The present theorem does
not import it. It is included for later work that needs the unconditional
semidirect decomposition.

## Provenance and scope

The target is the derived smooth-scheme formulation of the maximum-rank
argument of Borel and Tits, *Groupes réductifs* (1965), Theorem 3.13 and
Corollary 3.14, registered source `borel-tits-1965-groupes-reductifs`, as
described in the statement Markdown. The implemented route is the Library's
internal reduction described above. It uses Milne, *Algebraic Groups* (2017),
Theorem 16.27(b), printed p.333, and Theorem 16.33(a), (c), (d), printed
pp.335–336, through their published Library proofs and reductions; registered
source `milne-2017-algebraic-groups`. The target pair and all its imports are
unchanged.
