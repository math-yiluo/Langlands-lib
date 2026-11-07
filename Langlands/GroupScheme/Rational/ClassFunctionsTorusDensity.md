# Dense conjugates of a split maximal torus and class functions vanishing on it

This module works over a field `k : Type u` with a group scheme `G` over `Spec k`, a
commutative group scheme `T` over `Spec k`, and a homomorphism `j : T.toGrp ⟶ G`. All
declarations are in namespace `Langlands.GroupScheme.TorusConjugation`. The main
result is `classFunction_eq_zero`: over an algebraically closed field, an actual class
function on a connected reductive group that vanishes on a split maximal torus is
zero. The proof shows that the conjugates of the torus are dense.

## Provenance

This module is derived infrastructure. It supplies Lemma 6.2 of Steinberg, *Regular
elements of semisimple algebraic groups* (1965), §6, printed p. 62: the map from regular
class functions on `G` to regular functions on `T` is injective. Steinberg gets this
from the density of semisimple elements (his 2.14). The Lean proof takes a different
route that uses only published Library results. The conjugation morphism `G × T → G`
is surjective on tangent vectors at one regular torus point, so it has dense range, and
pullback along a dominant morphism into a reduced target is injective.

Standing hypotheses: the sections on tangent vectors and density assume
`[IsAffineHom G.X.hom]`. Results that use the torus coordinates take
`[IsAffineHom T.toGrp.X.hom]` explicitly, or derive it from `IsSplitTorus T.toGrp`.

## Conjugation and test points

- `conjugation j : G.X ⊗ T.toGrp.X ⟶ G.X` is the morphism `(g, t) ↦ g j(t) g⁻¹`.
  `comp_conjugation` and `lift_conjugation` compute it on points.
- `baseTest k` and `dualTest k` are the affine test objects `Spec k` and `Spec k[ε]`
  over `Spec k`. `basePoint t` turns an affine `k`-point into a rational point
  (`constantPoint_basePoint` recovers `t`). `augmentation` is the morphism
  `Spec k → Spec k[ε]` given by `ε ↦ 0`.
- `augmentation_comp_constantPoint`, `constantPoint_comp_hom` and
  `constant_constantPoint` give the behaviour of constant points under the augmentation,
  under homomorphisms, and under the constant map of the Lie package.
- `augmentation_comp_lieKernel` and `exists_lieKernel_of_augmentation`: a
  `k[ε]`-point of `H` is an element of the Lie kernel exactly when its augmentation is
  `1`. `lieKernelMapLinear_ofId_self` says that the coefficient change along the
  identity of `k` is the identity.

## Linear algebra at a regular point

- `mem_range_sub_id_of_eigen`: this is a generic lemma over any field `K` and module
  `V`. Suppose `B * A = 1` and `A X = c • X` with `c ≠ 0, 1`. Then `X` lies in the
  range of `B - 1`, because `X = (B - 1)((c⁻¹ - 1)⁻¹ • X)`.
- `exists_adjoint_sub_add` (hypotheses `[LocallyOfFiniteType G.X.hom]`,
  `IsSplitTorus T.toGrp`, a rational point `τ₀` of `T`, and `hreg`: every root of `j`
  takes a value different from `1` at `τ₀`). Every Lie vector `Z` of `G` can be written
  as `Ad(n⁻¹) ξ - ξ + W`, where `n = j(τ₀)` and `W` lies in `weightSpace j 0`. The proof
  uses the published direct-sum decomposition `isInternal_weightSpace_of_isSplitTorus`.
  Each weight space of a nonzero character `χ` is either zero or belongs to a root.
  `Ad(n)` acts on it by the scalar `χ(τ₀) ≠ 1`, and `basePointAdjoint_inv_mul` gives
  `Ad(n⁻¹) Ad(n) = 1`. By `mem_range_sub_id_of_eigen` such a weight space lies in the
  range of `Ad(n⁻¹) - 1`.

## Tangent surjectivity

`isTangentSurjectiveAt_conjugation` takes two hypotheses: `torusCentralizer j =
SubgroupFunctor.range j`, and the decomposition of `exists_adjoint_sub_add` at `τ₀`.
Under these hypotheses the conjugation morphism is surjective on rational tangent
vectors at the rational point `(1, τ₀)` of `G × T`, in the sense of the Library
predicate `IsTangentSurjectiveAt`. The proof runs as follows. Take a `k[ε]`-point `t`
of `G` over `n`, and let `C` be the constant `k[ε]`-point at `n`. Then `Z = C⁻¹ t`
lies in the Lie kernel. Decompose `Z = Ad(n⁻¹) ξ - ξ + W`. By
`Lie.mem_torusCentralizer_iff_mem_weightSpace_zero` and the centralizer hypothesis,
`W = j(σ₀)` for some `k[ε]`-point `σ₀` of `T`. Dividing `σ₀` by its constant part gives
a point `σ₁` that has trivial augmentation and maps to `W`. The `k[ε]`-point
`(ξ, τ₀ σ₁)` of `G × T` lies over `(1, τ₀)`. Its conjugation image is
`ξ C W ξ⁻¹ = t`, which uses the commutativity of the Lie kernel.

## Density

- `exists_regular` (`[IsAlgClosed k]`, `[LocallyOfFiniteType G.X.hom]`,
  `IsSplitTorus T.toGrp`): some rational point `τ₀` of `T` has every root value
  different from `1`. The set of roots is finite (`IsSplitTorus.finite_weightSupport`).
  The character lattice is finitely generated and torsion-free, so its group algebra
  `k[X]` is a domain of finite type. The product `∏ (single χ 1 - 1)` over the roots is
  nonzero because roots are nonzero. The published Nullstellensatz
  `BorelFieldExtension.exists_algHom_ne_zero` gives a `k`-algebra map `φ : k[X] → k`
  that does not kill the product. Let `τ₀` be the image of the universal torus point
  under `φ`. Then each `χ(τ₀) = φ(single χ 1)`, and none of these values is `1`.
- `denseRange_conjugation` (`[IsAlgClosed k]`, `IsConnectedReductive G`,
  `IsMaximalTorus j`, `IsSplitTorus T.toGrp`): the conjugation morphism has dense range.
  `G × T` is smooth (`smooth_tensor`) and `G` is irreducible
  (`DynamicConnected.irreducibleSpace_of_smooth`). The self-centralizing property comes
  from the published `maximalTorusCentralizer`. The published
  `denseRange_of_isTangentSurjectiveAt` then applies at `(1, τ₀)`.
- `pointCoordinates_eq_comp` and `pointCoordinates_universalPoint_injective` relate the
  point coordinates `Lie.pointCoordinates G` to the coordinate algebra used by
  `PointedCoordinateWeights`. Point coordinates of any point factor through evaluation
  at the universal point of `G.X`, and this evaluation is injective.
- `classFunction_eq_zero` (`[IsAlgClosed k]`, `IsConnectedReductive G`,
  `IsMaximalTorus j`, `IsSplitTorus T.toGrp`). Let `f : ClassFunctions.algebra G` vanish
  at `s ≫ j` for every commutative `k`-algebra `A : Type u` and every `A`-point `s` of
  `T`. Then `f = 0`. `G` is integral (`CharacterLatticeProof.isIntegral_of_smooth`),
  so it is reduced. The conjugation morphism is dominant, so its coordinate pullback is
  injective (`PointedCoordinateWeights.dominantPullbackStatement`). The pullback of
  `f` is its value at `g j(t) g⁻¹` for the universal point `(g, t)` of `G × T`. By
  conjugation invariance (`ClassFunctions.mem_algebra_iff_invariant`) this equals its
  value at `j(t)`, which is zero by hypothesis.
