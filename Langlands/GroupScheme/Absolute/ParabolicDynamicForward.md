# Parabolic subgroups are dynamic over their own field

Author: Worker 4153.

This internal helper module proves the forward direction of the published
`Langlands.GroupScheme.ParabolicDynamicStatement` (Milne, Theorem 25.1): every
parabolic subgroup is a dynamic parabolic of a cocharacter defined over the
original field. It is a composition of published Library proofs and adds no new
assertion from the literature. It does **not** prove
`ParabolicDynamicStatement` itself, whose converse direction (every dynamic
parabolic is parabolic) is not treated here. That full statement remains the
target of its own proof task.

## Declarations

All declarations are in namespace `Langlands.GroupScheme` and keep the
arbitrary universe `u`.

- The imported `splitParabolicCocharacterStatement : SplitParabolicCocharacterStatement.{u}`
  from [SplitParabolicCocharacterProof](SplitParabolicCocharacterProof.md).
  The published reduction `splitParabolicCocharacterStatement_of_absoluteBorelOvergroup`
  (module `Absolute.SplitParabolicCocharacterAbsoluteReduction`) has three
  structural hypotheses. All three are now published proofs:
  `borelConjugacy` (`Absolute.BorelConjugacyProof`),
  `absoluteBorelOvergroupCocharacter` (`Absolute.BorelOvergroupCocharacterProof`)
  and `maximalTorusBaseChange` (`Torus.MaximalBaseChangeProof`). Applying the
  reduction to them proves the fixed split-torus classification without
  hypotheses. For every field `k`, every connected reductive `G`, every split
  maximal torus `j : T → G`, and every parabolic `i : P → G` through which `j`
  factors, the classification gives an integral cocharacter `ν` of `T` with
  `SubgroupFunctor.range i = Dynamic.parabolic (ν ≫ j)` on every test scheme.

- `exists_cocharacter_range_eq_parabolic_of_isParabolicSubgroup k G hG P i hi`.
  For every field `k : Type u`, every group scheme `G` over `Spec k` with
  `IsConnectedReductive G`, and every `i : P ⟶ G` with
  `IsParabolicSubgroup i`, it gives a cocharacter
  `χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G` with
  `SubgroupFunctor.range i = Dynamic.parabolic χ`. This is an equality of
  subgroup functors on every test scheme over `Spec k`, and `χ` is defined over
  `k` itself. The field is arbitrary: any characteristic, perfect or not, and
  `G` need not be split.

## Proof of the forward direction

1. Reductivity makes `G` smooth, affine and connected. `IsParabolicSubgroup i`
   contains closedness of `i`, so the underlying morphism of `i` in
   `Over (Spec k)` is a monomorphism.
2. The published `parabolicMaximalTorus` gives a commutative group scheme `T`
   over `k`, a maximal torus `j : T → G`, and `f : T → P` with `f ≫ i = j`.
   `T` is affine because `j` is a closed immersion into the affine `G`.
3. The published `torusFiniteGaloisSplitting` gives a finite-dimensional
   Galois extension `K/k`, in the same universe, over which `T` splits. Its
   automorphism group is finite, which supplies the required `Fintype`
   instance.
4. Over `K`, the base change of `G` is connected reductive
   (`connectedReductiveFieldExtensionStatement`). The base change of `j` is a
   maximal torus (forward direction of `maximalTorusBaseChange`). The base
   change of `i` is parabolic (`parabolicFieldExtensionStatement`). The base
   change of `f` still factors `j` through `i`, by functoriality of base
   change. So `splitParabolicCocharacterStatement` over `K` gives an integral
   cocharacter `ν` of `T_K` with `range(i_K) = Dynamic.parabolic (ν ≫ j_K)`.
5. The published `exists_range_eq_parabolic_iff_finiteGaloisBaseChange`
   (module `Absolute.FixedTorusGaloisDescent`) descends this presentation to
   `k`. Its proof takes the integral Galois orbit sum of `ν`. This sum has the
   same nonnegative root region as `ν`, and it descends to a cocharacter `μ`
   of `T` over `k` with `range(i) = Dynamic.parabolic (μ ≫ j)`. The
   theorem returns `χ = μ ≫ j`.

## Provenance

This is an internal composition of the published Library theorems named
above. The mathematical statement is the forward direction of
J. S. Milne, *Algebraic Groups* (2017), Theorem 25.1, printed p.544. That
theorem is cited by the docstring of `ParabolicDynamicStatement`; the source is
registered as `milne-2017-algebraic-groups`. The implemented route follows
Milne's proof of this direction (same page). Milne takes a maximal torus `T`
inside `P` and a finite Galois extension `k'/k` over which `T` splits. He finds
a cocharacter `λ` of `T_{k'}` with `P_{k'} = P(λ)`. The sum of the Galois
conjugates of `λ` is then a cocharacter of `T` defined over `k` with the same
dynamic parabolic. Milne gets `P_{k'} = P(λ)` from the classification of the
parabolics that contain a Borel subgroup (his 21.91 and 21.92). Here that step
is the Library's fixed split-torus classification `splitParabolicCocharacterStatement`,
which is proved through the absolute Borel-overgroup classification.
