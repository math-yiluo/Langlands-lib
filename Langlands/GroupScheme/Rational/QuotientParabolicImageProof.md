# Proof: quotient maps carry parabolic and Borel subgroups to parabolic and Borel subgroups

`Langlands.GroupScheme.quotientParabolicImage : QuotientParabolicImageStatement.{u}` proves the
unchanged statement [`Rational.QuotientParabolicImageStatement`](QuotientParabolicImageStatement.md)
(Milne 2017, 17.69). The statement covers a field `k`, a homomorphism `q : G ⟶ Q` of smooth,
affine, connected groups over `k` that is flat and surjective, a homomorphism `i : H ⟶ G`, a
closed subgroup `j : H' ⟶ Q` with `H'` smooth, and a homomorphism `f : H ⟶ H'` that is surjective
on underlying spaces, with `i ≫ q = f ≫ j`. If `i` is parabolic, then so is `j`. If `i` is a
geometric Borel subgroup, then so is `j`.

The module adds one helper theorem,
`Langlands.GroupScheme.QuotientParabolicImage.isBorelSubgroup_image`, and the main theorem. It adds
no definitions or axioms. Everything else comes from published Library results and Mathlib.

The proof uses only that `q` is surjective. The flatness hypothesis is introduced but not used.
The proof does not go through Milne's Proposition 17.20. It shows that the image of a Borel
subgroup is Borel directly, using the properness criterion of Milne 17.19 (b) ⇒ (a).

## Helper: the image of a Borel subgroup over an algebraically closed field

`QuotientParabolicImage.isBorelSubgroup_image` works over an algebraically closed field `k`. Let
`G` and `Q` be smooth, affine and connected, and let `q : G ⟶ Q` be surjective on underlying
spaces. Let `i : B ⟶ G` be Borel (`IsBorelSubgroup`), `j : I ⟶ Q` a closed subgroup with `I`
smooth, and `f : B ⟶ I` surjective with `i ≫ q = f ≫ j`. Then `j` is Borel. The proof takes five
steps.

1. **`I` is connected.** `B` is connected (part of `IsBorelSubgroup`), and `I` is the continuous
   surjective image of `B` (Mathlib's `Function.Surjective.connectedSpace`).
2. **`I` is solvable.** `f` is locally of finite type: `f ≫ (I → Spec k)` equals the structure
   map of `B`, which is smooth (Mathlib's `locallyOfFiniteType_of_comp`). So
   `rationalPoints_surjective` ([`Absolute.QuotientNormalizer`](../Absolute/QuotientNormalizer.md))
   makes `f` surjective on `k`-points as a group homomorphism. By
   `isSolvableGroupScheme_iff_isSolvable_points`
   ([`Absolute.RationalPointClosureSolvable`](../Absolute/RationalPointClosureSolvable.md)), the
   solvability of `B` is solvability of the group `B(k)`. Its quotient `I(k)` is solvable
   (Mathlib's `Group.isSolvable_of_surjective`), and the same equivalence makes `I` solvable.
3. **`G/B` is proper.** `smoothSubgroupQuotientExistence`
   ([`HomogeneousQuotientProof`](../HomogeneousQuotientProof.md)) gives a separated quotient
   `p : G ⟶ X` of finite type. The map `p` is smooth, surjective and quasi-compact, and its
   fibres are exactly the cosets of `B`. A Borel subgroup is parabolic
   (`BruhatCovering.isParabolicSubgroup_of_isBorelSubgroup`,
   [`Absolute.BruhatCoveringSteps`](../Absolute/BruhatCoveringSteps.md)), so
   `parabolicSubgroupQuotientProper`
   ([`ParabolicQuotientProperProof`](../ParabolicQuotientProperProof.md)) makes `X` proper.
4. **`Q/I` is proper.** `smoothSubgroupQuotientExistence` gives a quotient `r : Q ⟶ R` with the
   same properties for `I ⊆ Q`. The composite `q ≫ r : G ⟶ R` is constant on the cosets of `B`:
   - if `g⁻¹ h = i(y)` on a test scheme, then `q(g)⁻¹ q(h) = q(i(y)) = j(f(y))`;
   - this point lies in `I`, so `q(g)` and `q(h)` have the same image in `R`.

   `FiniteIndexTransfer.exists_factor`
   ([`Absolute.FiniteIndexQuotientProperProof`](../Absolute/FiniteIndexQuotientProperProof.md))
   needs `p` flat, surjective and quasi-compact, with fibres inside the cosets. It then factors
   `q ≫ r = p ≫ ρ` for a morphism `ρ : X ⟶ R` over `k`. The composite `p ≫ ρ = q ≫ r` is
   surjective, so `ρ` is surjective (Mathlib's `Surjective.of_comp`). The structure map of `R`
   composed with `ρ` is the structure map of `X`, which is universally closed. So the structure
   map of `R` is universally closed (Mathlib's `UniversallyClosed.of_comp_surjective`). With
   separatedness and finite type, `R` is proper.
5. **Conclusion.** `properSolvableQuotientBorel`
   ([`Absolute.ProperSolvableQuotientProof`](../Absolute/ProperSolvableQuotientProof.md), Milne
   17.19 (b) ⇒ (a)) applies to the smooth, connected, solvable closed subgroup `j` with proper
   quotient `r`. So `j` is Borel.

## Main theorem

Let `F` be base change along `b = toAlgebraicClosure k : Spec k̄ ⟶ Spec k`
(`GroupScheme.baseChange b`). Base change preserves the structure needed by the helper:

- `F G`, `F Q` and `F H'` are smooth, and `F G` and `F Q` are affine. These are base changes of
  the structure morphisms, `pullback.snd`.
- `F G` and `F Q` are connected (`connectedSpace_baseChange_of_smooth_affine`,
  [`GeometricConnectedness`](../GeometricConnectedness.md)).
- `F q` is surjective (Mathlib's `MorphismProperty.overPullbackMap` for the base-change-stable
  property `Surjective`).
- `F j` is a closed subgroup (`IsClosedSubgroup.baseChange`,
  [`SubgroupBaseChange`](../SubgroupBaseChange.md)).

**Parabolic part.** Suppose `i` is parabolic
([`Absolute.Borel`](../Absolute/Borel.md), `IsParabolicSubgroup`). Then there is a Borel subgroup
`b₀ : B₀ ⟶ F G` that factors as `g₀ ≫ F i`. By `IsBorelSubgroup`, `B₀` is smooth and connected,
and `b₀` is a closed immersion. So `B₀` is affine over `k̄`, being a closed subscheme of the
affine `F G`. Likewise `F H'` is affine because `F j` is a closed immersion into the affine
`F Q`.

`HomImage.exists_image` ([`HomImage`](../HomImage.md)), applied to `g₀ ≫ F f : B₀ ⟶ F H'`, gives:

- a closed subgroup `inc : I ⟶ F H'` with `I` smooth;
- a surjective `fac : B₀ ⟶ I` with `fac ≫ inc = g₀ ≫ F f`.

Then `b₀ ≫ F q = g₀ ≫ F i ≫ F q = g₀ ≫ F f ≫ F j = fac ≫ (inc ≫ F j)`. The composite
`inc ≫ F j` is a closed subgroup, so the helper (with `F q`, `b₀`, `inc ≫ F j`, `fac`) makes it
Borel in `F Q`. It factors through `F j` by `inc`. Together with the hypotheses that `j` is a
closed subgroup and `H'` is smooth, this is `IsParabolicSubgroup j`.

**Borel part.** Suppose `i` is a geometric Borel subgroup
([`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), `IsGeometricBorelSubgroup`). Its second
component says `F i` is Borel in `F G`. `F f` is surjective by the same base-change argument, and
`F i ≫ F q = F f ≫ F j` by functoriality. The helper makes `F j` Borel in `F Q`. Since `j` is a
closed subgroup, `isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure`
([`Absolute.GeometricBorelDescent`](../Absolute/GeometricBorelDescent.md)) concludes that `j` is a
geometric Borel subgroup. That theorem also derives the ground-field component
`IsBorelSubgroup j` from the algebraic-closure one.

## Scope

This module proves exactly `QuotientParabolicImageStatement.{u}` for every universe `u`. It does
not prove the remaining clauses of Milne's Proposition 17.20 (maximal unipotent subgroups,
maximal tori, and the converse that every such subgroup of `Q` is an image). The helper
`isBorelSubgroup_image` is the Borel-image clause of 17.20 in the form above, over an
algebraically closed field.
