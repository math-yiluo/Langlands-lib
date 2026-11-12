# Proof of smooth real descent on actual reductive rational points

Author: Worker 4356.

`Langlands.Plancherel.rationalSmoothRealDescent` proves the Library proposition
`Langlands.Plancherel.RationalSmoothRealDescentStatement.{u}` (module
`Langlands.Representation.Plancherel.RationalSmoothRealDescentStatement`). It holds at an
arbitrary universe `u`, and its hypotheses are unchanged. This is Renard, *Représentations
des groupes réductifs p-adiques* (French edition dated 9 July 2026), V.3.19, printed p.115 /
PDF p.121, for actual connected reductive rational points.

Fix `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`, in mixed or equal characteristic. Fix
`M : GroupScheme (Spec (CommRingCat.of F))` with `hM : GroupScheme.IsConnectedReductive M`.
Give `GroupScheme.rationalPoints M` the canonical topology `rationalPointTopology F M.X`; the
affineness instances come from `hM`. Let `f : rationalPoints M →* Multiplicative ℝ` have open
kernel. The theorem proves both conclusions:

1. `rationalCommonNormKernel M ≤ f.ker`;
2. there is a unique `phi : rationalImageRealFunctionals M` with
   `phi (Additive.ofMul (rationalValuationImageProjection M g)) = (f g).toAdd` for every
   rational point `g`.

There is no splitness, tameness or characteristic restriction and no chosen embedding in
`GL_n`. The axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Implemented proof

The Lean proof is a single term. It applies a published conditional reduction to three
published unconditional proofs of its premises. No new lemma is introduced and no premise
remains.

### The reduction

`Langlands.Plancherel.rationalSmoothRealDescent_of_structure` (Worker 20, module
`Langlands.Representation.Plancherel.RationalSmoothRealDescentConstruction`) has type
`SmoothRealStructureStatement.{u} → RationalSmoothRealDescentStatement.{u}`. Its premise
`Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement.{u}` (module
`Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement`) is the conjunction of
the three universal local-point statements listed below. Write
`K = rationalCommonNormKernel M`, `Z = GroupScheme.schemeCenterPoints M` and
`D = (GroupScheme.derivedSubgroup M).carrier (Over.mk (𝟙 _))`. The reduction argues as
follows.

- An open kernel gives a discrete coset space. On a compact group it therefore has finite
  index. Every element raised to that index lies in the kernel. Since `Multiplicative ℝ` is
  torsion-free, the homomorphism is trivial there (`SmoothRealDescent.compact_subgroup_le_ker`).
  This gives `Z ⊓ K ≤ f.ker`.
- If an open subgroup contains a subgroup with compact coset space, its own coset space is
  compact and discrete, hence finite. No normality is used. The same torsion-freeness
  argument then applies (`SmoothRealDescent.eq_one_of_cocompact`). It is used for the
  restriction of `f` to `K` and the subgroup `((Z ⊓ K) ⊔ D).subgroupOf K`. That subgroup lies
  in the kernel because `Z ⊓ K ≤ f.ker` and `D ≤ f.ker`. This proves clause 1
  (`rationalCommonNormKernel_le_ker_of_structure`).
- Clause 2 follows from clause 1 by `existsUnique_rationalImageRealFunctional` (module
  `Langlands.Representation.Plancherel.RationalImageRealDescent`). Existence descends `f`
  through the surjection `rationalValuationImageProjection M`, whose kernel is `K`
  (`rationalValuationImageProjection_surjective` and `rationalValuationImageProjection_ker`,
  module `Langlands.Representation.Plancherel.RationalImageCharacters`). Uniqueness uses the
  same surjectivity.

### The three local-point structural inputs

Each is a published unconditional proof, imported by Lean name. Together they form the
anonymous-constructor proof of `SmoothRealStructureStatement.{u}`.

1. `Langlands.BruhatTits.RationalPoints.centralNormKernelCompactness` (module
   `Langlands.BruhatTits.RationalPoints.CentralNormKernelCompactnessProof`, Workers 1532 and
   1045) proves `CentralNormKernelCompactnessStatement.{u}`: `Z ⊓ K` is compact in the
   canonical topology. In the reduction it gives `Z ⊓ K ≤ f.ker` through the compact-subgroup
   argument.
2. `Langlands.BruhatTits.RationalPoints.centralDerivedNormKernelCocompactness` (module
   `Langlands.BruhatTits.RationalPoints.CentralDerivedNormKernelCocompactnessProof`, Worker
   4312) proves `CentralDerivedNormKernelCocompactnessStatement.{u}`: the quotient
   `K ⧸ (((Z ⊓ K) ⊔ D).subgroupOf K)` is compact. In the reduction it is the cocompact
   subgroup in the finite-index argument that gives clause 1.
3. `Langlands.BruhatTits.RationalPoints.derivedSmoothRealAnnihilation` (module
   `Langlands.BruhatTits.RationalPoints.DerivedSmoothRealAnnihilationProof`, Worker 4314)
   proves `DerivedSmoothRealAnnihilationStatement.{u}`: every open-kernel homomorphism to
   `Multiplicative ℝ` kills `D`. In the reduction it gives `D ≤ f.ker`.

The third input replaces Renard's step "trivial on commutators". It covers all rational
points of the scheme-theoretic derived subgroup, not only abstract commutators. None of the
inputs assumes finite index or rational-point surjectivity of a central isogeny.

## Correspondence with the source

Renard V.3.19 (printed p.115 / PDF p.121) justifies
`Hom_Z(Λ(M), R) = Hom_{Z,lisse}(M, R)` by showing that every smooth homomorphism from `M`
to `R` is trivial on `⁰M`. It uses four facts: `R(M)𝒟M` is cocompact in `M` with
`𝒟M ⊂ ⁰M`, hence `(R(M) ∩ ⁰M)𝒟M` is cocompact in `⁰M`; `R(M) ∩ ⁰M` is compact (proof of
V.2.6); smooth real homomorphisms are trivial on compact groups (lemma V.2.3); and
homomorphisms to `R` are trivial on commutators. It concludes by finite index and
torsion-freeness of `R`. Clause 1 is this assertion. Clause 2 is the identification itself,
read from smooth maps: every smooth map is `phi ∘ H_M` for exactly one additive `phi` on
`Λ(M)`.

The Lean route keeps the source's compact-group and finite-index steps, inside the
published reduction. It differs in two places.

- The scheme center `Z` replaces the radical `R(M)`. Its points contain those of the
  radical, so the compactness input for `Z ⊓ K` is a stronger claim and the cocompactness
  input is a weaker one. Both are proved.
- The commutator step is replaced by `derivedSmoothRealAnnihilation`, which kills the
  rational points of the scheme-theoretic derived subgroup. As the statement's Markdown
  explains, these can be more than the abstract commutators.

Cocompactness is a proved local-point input, not a consequence of the algebraic equality
`M = R(M)𝒟M`. This matters in positive characteristic, where an isogeny can have image of
infinite index on rational points.
