# Parabolic subgroups of connected reductive groups are the dynamic `P(χ)`: proof

Worker 3813, with Worker 4153 (named Worker 36 and Worker 3 before the
renumbering of 2026-11-08). The forward composition below is adapted from
Worker 4153's published helper module
[`Absolute.ParabolicDynamicForward`](ParabolicDynamicForward.md) (Task 4153).
This module uses different declaration names, so the two modules cannot clash.

`Langlands.GroupScheme.parabolicDynamic` proves exactly the published proposition
`Langlands.GroupScheme.ParabolicDynamicStatement.{u}` of
`Langlands.GroupScheme.Absolute.BorelStatement`, at its universe `u` and with
no added premise. Write `S = Spec (CommRingCat.of k)`. Take any field
`k : Type u`, any group scheme `G` over `S` with `IsConnectedReductive G`, and
any homomorphism `i : P ⟶ G` with `IsClosedSubgroup i`. The theorem proves

`IsParabolicSubgroup i ↔ ∃ χ : (Gm S).toGrp ⟶ G, SubgroupFunctor.range i = Dynamic.parabolic χ`.

The equality is the published equality of subgroup functors, so it holds on
every test scheme over `S`. The field is arbitrary: any characteristic, perfect
or not, and not necessarily algebraically closed. `G` need not be split. The
improper parabolic `P = G` and Borel subgroups are included. The only axioms
used are `propext`, `Classical.choice` and `Quot.sound`.

The proof combines published Library theorems. Each structural statement it
relies on is discharged by its published proof. None is a hypothesis of the
theorem. In particular `BorelConjugacyStatement` is the published theorem
`borelConjugacy`, not an assumption. The proof does not use
`RegularCocharacterBorelStatement`, `OppositeCellStatement` or
`MaximalSplitTorusConjugacyStatement` as premises.

## Declarations

All declarations are in namespace `Langlands.GroupScheme`.

- `ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup hG i hi`:
  for `hG : IsConnectedReductive G` and `hi : IsParabolicSubgroup i`, there is
  a cocharacter `χ : (Gm S).toGrp ⟶ G` defined over `k` with
  `SubgroupFunctor.range i = Dynamic.parabolic χ`.
- `parabolicDynamic : ParabolicDynamicStatement.{u}`: both directions.

## Forward direction: a parabolic subgroup is some `P(χ)` over `k`

This is the helper theorem
`ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup`.

1. `IsConnectedReductive G` makes `G` smooth, affine and connected.
   `IsParabolicSubgroup i` contains closedness of `i`. So the underlying
   morphism of `i` in `Over S` is a monomorphism.
2. The published `parabolicMaximalTorus` (module
   `Absolute.ParabolicMaximalTorusProof`, proving
   `ParabolicMaximalTorusStatement`) gives a commutative group scheme `T` over
   `k`, a maximal torus `j : T.toGrp ⟶ G`, and `f : T.toGrp ⟶ P` with
   `f ≫ i = j`. All of these are defined over `k` itself. `T` is affine over
   `S` because `j` is a closed immersion into the affine `G`.
3. The published `torusFiniteGaloisSplitting` (module
   `Torus.FiniteGaloisSplittingProof`) gives a field `K : Type u` with a
   finite-dimensional Galois algebra structure over `k` such that `T_K` is a
   split torus. The group `K ≃ₐ[k] K` is finite. `Fintype.ofFinite` gives the
   `Fintype` instance that the descent theorem needs.
4. Over `K`, write `F` for base change along `Spec K → Spec k`.
   - `F.obj G` is connected reductive, by the published
     `connectedReductiveFieldExtensionStatement` (module
     `Reductive.FieldExtensionProof`).
   - `F.map j` is a maximal torus, by the forward direction of the published
     `maximalTorusBaseChange` (module `Torus.MaximalBaseChangeProof`).
   - `F.map i` is parabolic, by the published
     `parabolicFieldExtensionStatement` (module
     `Absolute.ParabolicFieldExtensionProof`).
   - `F.map f ≫ F.map i = F.map j` holds by functoriality of base change.
5. The published reduction `splitParabolicCocharacterStatement_of_absoluteBorelOvergroup`
   (module `Absolute.SplitParabolicCocharacterAbsoluteReduction`) has three
   premises. The published proofs `borelConjugacy`
   (`Absolute.BorelConjugacyProof`), `absoluteBorelOvergroupCocharacter`
   (`Absolute.BorelOvergroupCocharacterProof`) and `maximalTorusBaseChange`
   discharge them, which gives `SplitParabolicCocharacterStatement.{u}`.
   Over `K`, apply it to the split maximal torus `F.map j` and the parabolic
   `F.map i`. This gives an integral cocharacter `ν` of `T_K` with
   `range(F.map i) = Dynamic.parabolic (ν ≫ F.map j)`.
6. The reverse direction of the published
   `exists_range_eq_parabolic_iff_finiteGaloisBaseChange` (module
   `Absolute.FixedTorusGaloisDescent`) descends this presentation to `k`. It
   needs `G` smooth, affine and connected, `T` affine, `i` monic and `T_K`
   split. Its construction takes the integral Galois orbit sum of `ν`, which
   descends to a cocharacter `μ` of `T` over `k`. The result is
   `range i = Dynamic.parabolic (μ ≫ j)` on all test schemes. The theorem
   returns `χ = CommGroupScheme.groupHom μ ≫ j`.

## Reverse direction: every `P(χ)` with a closed representative is parabolic

Suppose `SubgroupFunctor.range i = Dynamic.parabolic χ`. The published
`isParabolicSubgroup_of_range_eq_dynamicParabolic` (module
`Absolute.DynamicParabolicRecognition`) takes `hG`, the closedness hypothesis
`IsClosedSubgroup i` of the target statement, `χ` and this equality. It returns
`IsParabolicSubgroup i`. Its proof shows that `P` is smooth (`dynamicSmooth`).
It then constructs a Borel subgroup of `G_{k̄}` inside the base-changed dynamic
parabolic, for `k̄ = AlgebraicClosure k`, and factors it through the base
change of `i`.

## Provenance

This is an internal composition of the published Library theorems named above.
It adds no new assertion from the literature. The proved proposition is
J. S. Milne, *Algebraic Groups* (2017), Theorem 25.1, printed p.544 (PDF
p.560), source `milne-2017-algebraic-groups`, in the range formulation of the
statement's Markdown (section 4 of `Absolute/BorelStatement.md`). The
implemented route follows the structure of Milne's proof. For the converse,
Milne takes a maximal torus `T` in `P`, a finite Galois extension `k'` of `k`
splitting `T`, a cocharacter `λ` of `T_{k'}` with `P_{k'} = P(λ)` (his 21.91
and 21.92), and the sum of the Galois conjugates of `λ`. These are steps 2, 3,
5 and 6 of the forward direction above. Step 5 replaces Milne's appeal to 21.91
and 21.92 with the Library's split-torus classification. To show that `P(χ)` is
parabolic, Milne places the Borel subgroup `P(λ')` of a regular cocharacter
`λ'` close to `λ` inside `P(λ)` over an algebraically closed field. The
published recognition theorem uses this regular-refinement construction over
`AlgebraicClosure k`.
