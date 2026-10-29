# Proof of the normalized quasicuspidal embedding in a product Levi

Author: Worker 917.

This module proves the published proposition
`Langlands.CuspidalSupport.NormalizedRefinedQuasicuspidalEmbeddingTheorem`
from
[`RefinedQuasicuspidalEmbeddingStatement`](RefinedQuasicuspidalEmbeddingStatement.md).
The main theorem is

```
theorem Langlands.CuspidalSupport.normalizedRefinedQuasicuspidalEmbedding
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    NormalizedRefinedQuasicuspidalEmbeddingTheorem.{uF, uV} F T
```

Its type is exactly the target proposition, with the same independent
universe levels `uF` and `uV`. There are no extra hypotheses. A declaration
check found that it uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The module does not change the statement pair or any module
that the statement imports.

The target says the following. Install `T.topology` and fix any rank `n`,
any block shape `B` and any irreducible smooth `ω` of `B.Levi F.Carrier`.
Then there are a refinement `S`, an irreducible smooth quasicuspidal `σ` of
the flattened Levi `(B.flatten S).Levi F.Carrier`, and an injective
intertwining map from `ω` into
`T.normalizedRefinedInduced B S (σ.representation.comp e.symm.toMonoidHom)`,
where `e := Geometric.flattenedLeviEquiv F.Carrier B S`.

## Declarations

All auxiliary declarations live in the namespace
`Langlands.CuspidalSupport.RefinedQuasicuspidalEmbedding`.

- `flattenedLeviEquiv_eq_leviRefinementEquiv R B S`: for any commutative
  ring `R`, the target's equivalence `Geometric.flattenedLeviEquiv R B S`
  equals the descent statement's equivalence
  `GeneralLinear.BlockShape.leviRefinementEquiv (B.flatten S) B S
  (B.flattenBlockEquiv S) (fun q => (B.flatten_size_flattenBlockEquiv S q).symm) R`.
  Both are equivalences from the flattened Levi onto the refined Levi.
- `flattenedJacquet T B S ρ` (an `abbrev`): the normalized refined Jacquet
  action `T.normalizedRefinedJacquet B S ρ`, pulled back to the flattened
  Levi along `e`, that is `(T.normalizedRefinedJacquet B S ρ).comp
  e.toMonoidHom`. Its carrier is `RefinedJacquetModule B S ρ`.
- `flattenedJacquet_symm`: the flattened action at `e.symm m` is the
  refined action at `m`.
- `refinedJacquetMk_parabolic_mem`: a subrepresentation `U` of
  `flattenedJacquet T B S ρ` that contains the class of `v` also contains
  the class of `ρ q v`, for every `q` in the refined parabolic.
- `exists_finset_generating T B S hρ v₀ hgen`: if `ρ` is smooth and every
  vector lies in the linear span of the orbit of `v₀`, then a finite set of
  classes generates `flattenedJacquet T B S ρ`. Precisely, every
  subrepresentation containing that finite set is `⊤`.
- `Langlands.CuspidalSupport.normalizedRefinedQuasicuspidalEmbedding`: the
  main theorem displayed above.

The module ends with an `example` that checks the specialization
`NormalizedRefinedQuasicuspidalEmbeddingTheorem.{uF, max uF uV} F T`.

## The proof

The proof follows BZ76 Proposition 3.19: descent, finite generation, an
irreducible quotient, and first adjointness. Each step uses a Library result
by its Lean name. The new content is the coordinate agreement, the finite
generation argument for refined Jacquet modules of product Levis, and the
assembly.

### 1. Descent

Install `T.topology`. Fix `n`, `B`, `ω` and `hω : ω.IsIrreducible`, and write
`ρ := ω.representation`. The carrier of `ω` is nontrivial by
`QuasicuspidalEmbedding.nontrivial_of_isIrreducible`, since an irreducible
representation is nonzero. The published theorem
`CuspidalSupport.minimalNonzeroRefinedJacquet F T`, applied to `n`, `B` and
`ω`, gives a refinement `S : BlockRefinement B` with:

- `RefinedJacquetModule B S ρ` nontrivial, and
- `IsLeviQuasicuspidal (B.flatten S)
  ((T.normalizedRefinedJacquet B S ρ).comp (leviRefinementEquiv …).toMonoidHom)`.

This `S` is the refinement in the conclusion. Descent needs neither
irreducibility nor admissibility of `ω`, only nontriviality.

### 2. Coordinate transport

Descent pulls the action back along `leviRefinementEquiv`. The target uses
`flattenedLeviEquiv`. The lemma `flattenedLeviEquiv_eq_leviRefinementEquiv`
proves that the two are the same equivalence; this is a proof, not an
assumption. Two elements of the refined Levi are equal when their images
under `(refinedLeviEquiv R B S).symm` agree in each outer block `i` and each
inner block `j`. On one side `flattenedLeviEquiv_component` gives the block
`B.flattenBlockEquiv S ⟨i, j⟩` of `m`, reindexed along
`finCongr (B.flatten_size_flattenBlockEquiv S ⟨i, j⟩)`. On the other side
`leviRefinementEquiv` is `nestedLeviEquiv` followed by `refinedLeviEquiv`, and
`nestedLeviEquiv_apply` gives the same block, reindexed along
`finCongr ((B.flatten_size_flattenBlockEquiv S ⟨i, j⟩).symm.symm)`. The two
expressions agree, and `simp` closes the goal.

Write `τ := flattenedJacquet T B S ρ` for the action of the flattened Levi on
`RefinedJacquetModule B S ρ`. Rewriting with the lemma turns the descent
conclusion into `IsLeviQuasicuspidal (B.flatten S) τ`.

`τ` is smooth. `T.isSmooth_normalizedRefinedJacquet` shows that the refined
action is smooth, and `Langlands.isSmooth_comp` shows that pulling back along
the continuous homomorphism `e` keeps smoothness. Continuity of `e` comes
from the topological equivalence
`Geometric.flattenedLeviEquivContinuous F.Carrier B S`, whose underlying
multiplicative equivalence is `e`. Let `J := SmoothRep.of τ hτ`.

### 3. Finite generation

This is the analogue of BZ76 3.13(e) for the Jacquet module of a
representation generated by one vector. The Lean argument is
`exists_finset_generating`.

Pick a nonzero `v₀ : ω`. Since `ω` is irreducible,
`QuasicuspidalEmbedding.mem_span_orbit` puts every vector in the linear span
of `{ρ g v₀}`. Smoothness of `ω` gives an open subgroup `K` of
`B.Levi F.Carrier` fixing `v₀`. The coset space of the refined parabolic `P`
is compact by `Parabolic.refinedParabolicQuotientCompact F T B S`.
`Induction.exists_finset_doubleCoset_cover` then gives a finite set `t` with
`B.Levi F.Carrier = ⋃_{i ∈ t} P i K`. The candidate generators are the
classes of the vectors `ρ i v₀` for `i ∈ t`.

Let `U` be a subrepresentation of `τ` that contains these classes. Write
`g = q i k` with `q ∈ P`, `i ∈ t` and `k ∈ K`. Then `ρ g v₀ = ρ q (ρ i v₀)`,
because `k` fixes `v₀`. `refinedJacquetMk_parabolic_mem` shows that the
class of `ρ q (ρ i v₀)` lies in `U`. Its proof has two steps:

- `Parabolic.FirstAdjointness.refinedJacquetMk_parabolic` replaces `q` by its
  Levi component `π q`, since the unipotent part acts trivially on classes;
- `Parabolic.FirstAdjointness.refinedJacquetMk_levi` writes the class of
  `ρ (π q) w` as `χ(π q) • (T.normalizedRefinedJacquet B S ρ (π q))
  (class of w)`, where `χ = T.refinedLeviHalfModulus B S`. By
  `flattenedJacquet_symm` this is the scalar `χ(π q)` times `τ(e⁻¹(π q))`
  applied to the class of `w`. `U` is stable under `τ` and under scalars.

So `U` contains the class of every orbit vector `ρ g v₀`. The preimage of
`U` under the quotient map is a linear subspace containing the orbit of
`v₀`, so it contains the span, which is all of `ω`. The quotient map
`Jacquet.mk` is surjective, so `U = ⊤`.

### 4. An irreducible quasicuspidal quotient

`J` is nontrivial by step 1, and it is generated by a finite set by step 3.
`QuasicuspidalEmbedding.exists_isCoatom_subrepresentation` gives a
subrepresentation `U` of `J` that is a coatom, that is, a maximal proper
subrepresentation. Let `σ := SmoothRep.quotient J U`, with quotient map
`q := SmoothRep.hom (SmoothRep.mkQ J U)`. It is surjective
(`SmoothRep.mkQ_surjective`), its kernel is `U`
(`Submodule.Quotient.mk_eq_zero`), and `σ` is smooth because it is an object
of `SmoothRep`. The carrier of `σ` is the quotient of
`RefinedJacquetModule B S ρ` by `U`, and it lies in `Type uV`.

- `σ` is irreducible by `QuasicuspidalEmbedding.isIrreducible_of_isCoatom`.
  This is the source's irreducible quotient (BZ76 2.6).
- `σ` is quasicuspidal: for every refinement `S'` of `B.flatten S` with
  proper refined parabolic, the coinvariants of `τ` are a subsingleton by
  step 2. `QuasicuspidalEmbedding.coinvariants_subsingleton_of_surjective`
  passes this to the quotient `σ`.

### 5. First adjointness, with the normalizations

Let `σ' := σ.representation.comp e.symm.toMonoidHom`, the representation of
the refined Levi used by the target. The quotient map `q` is also an
intertwining map `A` from `T.normalizedRefinedJacquet B S ρ` to `σ'`.
Indeed, for `m` in the refined Levi, `flattenedJacquet_symm` rewrites the
refined action at `m` as `τ(e⁻¹ m)`. `q` intertwines `τ(e⁻¹ m)` with
`σ(e⁻¹ m) = σ'(m)`. In Lean, `A` has the same underlying linear map as `q`.

Install `T.leviTopologicalGroup B`. The published refined Frobenius map gives

`j := Parabolic.FirstAdjointness.refinedFrobenius T B S ω.isSmooth A :
ω.representation.IntertwiningMap (T.normalizedRefinedInduced B S σ')`.

This is the actual normalized refined induction of the target, not abstract
induction or another coordinate model. Its value at `v` is the smooth
function `g ↦ A(class of ρ g v)` (`refinedFrobenius_eval`).

**Normalized covariance and the right action.** The refined Jacquet action
is normalized by the inverse half modulus. `normalizedRefinedJacquet_mk`
gives `(T.normalizedRefinedJacquet B S ρ m)(class of v) =
χ(m)⁻¹ • class of ρ m v`, with `χ = T.refinedLeviHalfModulus B S`. Induction
uses the positive half modulus. Its functions satisfy
`f(q g) = χ(π q) • σ'(π q)(f g)` for `q` in the refined parabolic, and
`G = B.Levi F.Carrier` acts by right translation, `(g • f)(x) = f(x g)`.
The two factors cancel in `refinedJacquetMk_levi`, which says that the class
of `ρ m v` is `χ(m) • (T.normalizedRefinedJacquet B S ρ m)(class of v)`.
The published lemma `refinedJacquet_covariant` uses it to prove that
`g ↦ A(class of ρ g v)` has exactly this positive half-modulus covariance.
That function intertwines `ρ` with right translation, because
`ρ (x g) = ρ x ∘ ρ g`. These facts are part of the published construction of
`refinedFrobenius` in `Parabolic.NaturalFirstAdjointness`, which this module
reuses without change. Step 3 uses the same cancellation, through
`refinedJacquetMk_levi`, to stay inside a subrepresentation of `τ`.

### 6. Injectivity

Mathlib's `Representation.IsIrreducible.injective_or_eq_zero`, applied to
the irreducible `ω.representation`, says that `j` is either injective or
zero. Suppose `j = 0`. `U` is a coatom, so `U ≠ ⊤` and some class `x` is not
in `U`. Write `x` as the class of some `v` (`Jacquet.mk_surjective`). By
`refinedFrobenius_eval` at `g = 1`, `(j v)(1) = A(class of v) = q x`. As
`j v = 0`, this gives `q x = 0`, so `x ∈ U`, a contradiction. Hence `j` is
injective. The theorem returns `S`, `σ`, `σ.IsIrreducible`, the
quasicuspidality of `σ`, and `j` with its injectivity.

## Universes

`uF` is the universe of `F.Carrier`, so all Levi groups lie in `Type uF`.
The carriers of `ω` and `σ` lie in `Type uV`: the carrier of `σ` is a
quotient of the refined Jacquet module, which is itself a quotient of the
carrier of `ω`. The induced representation's carrier is a type of functions
on `B.Levi F.Carrier` and lies in `Type (max uF uV)`. The theorem is
universe polymorphic in independent `uF` and `uV`. The final `example`
instantiates it at `uV := max uF uV` and elaborates
`NormalizedRefinedQuasicuspidalEmbeddingTheorem.{uF, max uF uV} F T`.

## Rank zero, the empty shape and whole-product refinements

The proof has no case split on `n`, on `B` or on `S`, and it uses no
positivity hypothesis. The same steps cover the boundary cases.

- At rank zero, `B.length = 0` and `B.Levi F.Carrier` is the one-element
  group. Descent returns the empty refinement, the flattened shape is empty,
  the refined parabolic is the whole group and the unipotent subgroup is
  trivial. The Jacquet module is the carrier of `ω`, modulo the zero
  subspace. Compactness and the double-coset cover hold trivially, and an
  irreducible quotient of the irreducible `ω` is still produced by the coatom
  argument. `IsLeviQuasicuspidal` of the empty flattened shape is vacuous.
  The elementary direct argument described in the statement Markdown (trivial
  `σ`, constant functions) is not used. The uniform proof covers this case.
- If descent returns a whole-product refinement, in which every `S i` has a
  single block, the same argument applies. Then the refined parabolic is the
  whole group, and the conclusion embeds `ω` into the induction of `σ'` from
  the whole group.

## Imports and dependency audit

The module imports exactly:

1. `Langlands.Representation.CuspidalSupport.RefinedQuasicuspidalEmbeddingStatement`:
   the target statement.
2. `Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetProof`:
   `minimalNonzeroRefinedJacquet` (descent). This is the sole exact proof of
   statement task `c43a11db-57cf-4226-bc67-99ecbe26674f`, published by proof
   task `6a99fcfb-592f-4070-8d08-2ed1cf2869c1`. It is not duplicated.
3. `Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof`:
   only its generic lemmas `nontrivial_of_isIrreducible`, `mem_span_orbit`,
   `exists_isCoatom_subrepresentation`, `isIrreducible_of_isCoatom` and
   `coinvariants_subsingleton_of_surjective`, which hold for an arbitrary
   group `G`. Its GL-input finite-generation and orbit-function
   constructions are not used.
4. `Langlands.Representation.Parabolic.NaturalFirstAdjointness`:
   `refinedFrobenius`, `refinedFrobenius_eval`, `refinedJacquetMk_parabolic`
   and `refinedJacquetMk_levi`. These have no admissibility premise.
5. `Langlands.Representation.Parabolic.RefinedInductionAdmissibility`: only
   `refinedParabolicQuotientCompact`, compactness of the refined parabolic
   coset space, which is proved from compactness of the integral groups.
   Its admissibility-preservation theorem is not used.
6. `Langlands.Representation.Smooth.Transfer.PullbackProof`:
   `isSmooth_comp`.

Other names come through these imports: `Induction.exists_finset_doubleCoset_cover`
(`Induction.CompactQuotientProof`), `SmoothRep.quotient`, `SmoothRep.mkQ`
and `SmoothRep.mkQ_surjective` (`Category.Subquotients`),
`Geometric.flattenedLeviEquiv`, `flattenedLeviEquiv_component` and
`flattenedLeviEquivContinuous` (`Geometric.FlattenedLevi`), and
`BlockShape.leviRefinementEquiv` and `BlockShape.nestedLeviEquiv_apply`
(`Group.GL.RefinementCoordinates`).

The project import closure of these six imports was computed from the
`import` lines of the Library at commit
`e40be87d4e73ac457e91929eddf904bd95d12d2f`. It has 88 project modules. Its
only Classification modules are `Classification.Supercuspidal` and
`Classification.SupercuspidalTwist`, both already in the closure of the
published descent proof. The closure contains no module of:

- the arbitrary irreducible-Levi admissibility task
  `3b437c95-1157-464c-9ae4-828ebd7b638d`, including
  `IrreducibleLeviAdmissibilityStatement`;
- finite-length admissibility `d9898ee2-c630-49a3-a9d3-e699b53c02db`, or the
  all-smooth parabolic finite-length statement and proof
  (`58159589-1602-4756-a82a-36705038ce59`,
  `2a216dfa-5b20-4b4b-9ff8-50b41a0b28f7`);
- admissible factorization, or second adjointness with an admissibility
  premise;
- analytic segment classification, special-head multisegment exhaustion,
  ordered strong-head existence, quotient coverage, tempered block
  uniqueness, the square-integrable Langlands classification,
  square-integrable exhaustion or regular exhaustion.

A text search of all 88 modules for `FiniteLength`, `AdmissibleFactorization`,
`IrreducibleLeviAdmissib`, `Exhaustion`, `SquareIntegrable`, `Tempered` and
`SecondAdjoint` found only definitions:

- `HasFiniteLength` in `Category.Basic`;
- the Prop-valued `CuspidalInductionLengthTheorem` in
  `CuspidalSupport.NormalizedCuspidalInductionStatement`;
- the Prop-valued `UnipotentExhaustionClause` in
  `Parabolic.GeometricPrerequisitesStatement`, which is about unipotent
  subgroups.

None of these is used as a hypothesis or a proof input here. The proof uses
admissibility nowhere, and its conclusion asserts no admissibility or finite
length.

## Sources and adaptations

- BZ76: I. N. Bernshtein and A. V. Zelevinskii, *Representations of the
  group GL(n,F) where F is a non-Archimedean local field*, Russian Math.
  Surveys 31:3 (1976), 1–68. Literature ID
  `bernstein-zelevinsky-1976-representations-gln`. Proposition 3.19, p.34,
  and its proof; 3.13(b),(e), pp.32–33; 3.6, p.30; 2.6.
- BZ77: I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
  reductive p-adic groups. I*, Ann. Sci. ENS (4) 10 (1977), 441–472.
  Literature ID `bernstein-zelevinsky-1977-induced-i`. 1.8, printed p.444,
  gives the normalized conventions.

The source proof of 3.19 chooses a minimal partition `β` with
`r_{β,α}(π) ≠ 0`. It gets quasicuspidality from transitivity 3.13(c),
finite generation from 3.13(e), an irreducible quotient from 2.6, and the
embedding from 3.13(b). The Lean proof has the same shape, with these
adaptations:

- Descent is the published `minimalNonzeroRefinedJacquet`, which includes
  the quasicuspidality of the pulled-back Jacquet module. Transitivity is
  not invoked here.
- Finite generation is proved only for the module needed. The irreducible
  `ω` is generated by one smooth vector, so its Jacquet module is generated
  by finitely many classes. This uses compactness of the refined parabolic
  coset space, the analogue of 3.6. It is derived content and is not stated
  in this form in the source.
- The source uses unnormalized induction and Jacquet functors. The Lean
  proof uses the normalized functors of BZ77 1.8 directly: the Jacquet action
  carries the inverse half modulus and induction the positive half modulus,
  and `refinedFrobenius` accounts for their cancellation (step 5). No twist
  of `σ` is needed, so the twist conversion described in the statement
  Markdown is not used.
- The coordinate agreement of step 2 is internal to the Library's two
  coordinate models. It has no counterpart in the source, which identifies
  `G_β` with its natural embedding.
