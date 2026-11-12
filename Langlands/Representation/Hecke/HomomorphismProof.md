# Continuous-homomorphism Hecke adjunctions and pullback comparison

Worker 132, Task 5401.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, III.2.1, printed p.70 / PDF p.76, using I.2.3, printed pp.17–18 / PDF pp.23–24; registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The theorem `Langlands.Hecke.Homomorphism.continuousHomomorphismStatements` has the exact published target `Langlands.Hecke.Homomorphism.ContinuousHomomorphismStatements`. It proves the two canonical Hecke adjunctions and the smooth pullback comparison and transported adjunctions in Renard III.2.1. The group universes `uG` and `uH` and the parameter `v` are independent. As prescribed by the statement, the smooth functors use carrier universe `max uG v`, which is stable under tensoring with the actual `H(G)`.

The first conjunct, `heckeInductionAdjunctionStatement`, specializes `NondegenerateInductionAdjunction.FProof.canonical` and `PProof.canonical` to the published left and right subgroup Hecke actions. Their published commutation and nondegeneracy proofs supply the hypotheses. This retains the Chapter I additive Hom correspondences, inverse quotient lifts, naturality, unit and counit formulas and triangular identities.

The comparison is derived from the existing actions and quotient; it is an internal proof construction rather than an additional assertion attributed to the source. For a smooth representation `V`, `actionEvaluation` sends a Hecke function `b` to its integrated action on a fixed vector `m`. The published left-translation formula proves that evaluation intertwines the restricted left regular representation with `V` restricted along the continuous homomorphism.

Integrating this evaluation intertwiner proves equivariance for the subgroup Hecke algebra. Together with associativity of the original Hecke action, it lets `NonUnitalBimoduleTensor.leftLift` construct `contractionHom` on the actual balanced quotient, with formula `b ⊗ m ↦ b • m`. The published `RegularTensorContraction.contraction_injective` proves injectivity on this quotient. Original nondegeneracy supplies a fixing idempotent for each `m`, whose pure tensor with `m` proves surjectivity.

The additive inverse of this bijective map is subgroup Hecke linear because the forward map is injective and Hecke linear. This gives `contractionIso`. Its naturality follows by checking pure tensors: the required equality is precisely the integrated-action intertwiner identity for the original map of smooth representations. Thus `heckePullbackComparison` compares the given tensor functor with the integrated smooth pullback.

The proven III.1.4 equivalence for the specific functor `heckeNondegenerateModuleFunctor` supplies both equivalence conclusions in the smooth statement. `Iso.compInverseIso` composes the Hecke comparison with the inverse equivalence of `H` and its unit isomorphism. Reversing this yields `smoothPullbackComparison`, from the original restriction functor to the specified transported tensor functor `smoothF`. The two smooth adjunctions compose the published algebraic adjunctions with the equivalence adjunctions of `G` and `H`, in the directions required by `smoothF ⊣ smoothI` and `smoothP ⊣ smoothPseudoF`.
