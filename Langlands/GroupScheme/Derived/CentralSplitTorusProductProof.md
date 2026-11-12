# Proof of the derived and central split-torus product isogeny

Author: Worker 4420.

Module `Langlands.GroupScheme.Derived.CentralSplitTorusProductProof`.

## Result

`Langlands.GroupScheme.derivedCentralSplitTorusProduct` has type exactly
`DerivedCentralSplitTorusProductStatement.{u}`, the published proposition of
[`Derived.CentralSplitTorusProductStatement`](CentralSplitTorusProductStatement.md),
at an arbitrary universe `u`. Fix a field `k : Type u`, group schemes `G` and
`D` over `Spec k` with `IsConnectedReductive G`, and `d : D ⟶ G` with
`IsDerivedSubgroup d`. Fix commutative group schemes `S`, `S_D` and `A` and
morphisms `i`, `j`, `e`, `a` and `c`, where:

- `i` and `j` are maximal split tori;
- `CommGroupScheme.groupHom e` is a closed subgroup;
- `j ≫ d = CommGroupScheme.groupHom e ≫ i`;
- `a` is a split component;
- `CommGroupScheme.groupHom c ≫ i = a`.

Then the actual multiplication homomorphism
`prodHom (groupHom e) (groupHom c) : S_D × A → S` satisfies
`IsCentralIsogeny`. That is, it is finite, flat, surjective and locally of
finite presentation, and its full scheme-theoretic kernel is central on every
test scheme. No premise is added to the statement.

## Proof

The proof composes three published results and does not reprove the
mathematics of Conrad–Gabber–Prasad, Theorem C.2.15. The route differs from the
source proof, as described below.

1. **Reduction to surjectivity.** `derivedCentralSplitTorusProductReduction`
   (module [`Derived.CentralSplitTorusProductReduction`](CentralSplitTorusProductReduction.md))
   takes exactly the data and hypotheses of the target. It proves that the
   multiplication map is a central isogeny if and only if its underlying scheme
   map is surjective. The proof uses the forward implication (`.mp`). That
   module establishes finiteness, flatness, local finite presentation and
   centrality of the full kernel.
2. **Surjectivity from relative reflections.**
   `splitProduct_surjective_of_relative_reflections` (module
   [`Derived.CentralSplitTorusProductSurjectivity`](CentralSplitTorusProductSurjectivity.md))
   proves surjectivity of the underlying scheme map. It takes the hypotheses
   `hG`, `hd`, `hi`, `hj`, the compatibility `j ≫ d = groupHom e ≫ i`, `ha` and
   `hc`. Its one further premise says that every actual relative root
   `α ∈ relativeRoots i` has an actual relative Weyl element `w` with
   `IsRelativeReflection i α w`.
3. **Existence of the reflections.** The published unconditional theorem
   `relativeRootSystem : RelativeRootSystemStatement.{u}` (module
   [`Rational.RelativeRootSystemProof`](../Rational/RelativeRootSystemProof.md)),
   applied to `k`, `G`, `hG`, `S`, `i` and `hi`, gives
   `HasRelativeRootSystem i`.
   `HasRelativeRootSystem.exists_isRelativeReflection` (module
   [`Rational.RelativeReflectionProperties`](../Rational/RelativeReflectionProperties.md))
   turns it into the premise of step 2 for every relative root.

The premise of step 2 and the type of `relativeRootSystem` are stated under the
local instances `IsAffineHom G.X.hom` (from `hG.isAffineHom`) and
`Mono i.hom.hom.left` (from `hi.isSplitSubtorus.mono`). The proof introduces
the same two local instances before applying the lemmas.

## Relation to the source

The target is a derived reformulation of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Theorem C.2.15 with Step 1
of its proof; see the statement's Markdown for the citation and translation.
That proof works with the source's canonical subtorus `(S ∩ D(G))⁰_red` and
its maximal central split torus. The proof here never constructs those
canonical subgroups. Surjectivity comes from the published Weyl-norm argument
in step 2: the norm over the finite relative Weyl group is central, and the
complementary endomorphism is derived-valued. Together they factor a nonzero
power map of `S` through the supplied product. Finiteness and the remaining
isogeny conditions come from the full-kernel results of step 1. The supplied
factors are used as given.

## Scope

The universe `u` and the field `k` are arbitrary, including imperfect fields
and positive characteristic. Every compatible actual derived subgroup, pair of
maximal split tori and split component quantified in the target is retained.
The kernel's centrality holds on all test schemes, including nonreduced ones.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.
