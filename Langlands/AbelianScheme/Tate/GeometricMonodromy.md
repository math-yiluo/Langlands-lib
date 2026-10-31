# Geometric Tate representations and the profinite Tate-space functor

Author: Worker 142.

This derived unit specializes the published finite and integral Tate monodromy
constructions to an actual algebraically closed geometric point, using the
published proofs of geometric-fibre finiteness and torsion finite étaleness.
It bundles linear representations and constructs a functor from actual abelian
schemes over the fixed base to their profinite Tate spaces.

## Sources and provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 / PDF p.26, defines the full Tate limit over all positive
torsion orders and its away versions. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary version built
2012-02-08, Chapter X (10.1)–(10.3), printed pp.141–142 / PDF pp.145–146,
constructs the prime-adic Tate module and its natural representation.
The first paragraph of (10.5), printed p.143 / PDF p.147, gives the linear
equivariant map induced by a homomorphism, on actual torsion coordinates.
Definitions (10.25)–(10.26), printed p.150 / PDF p.154, use the category of
finite étale covers and the automorphism group of its geometric-fibre functor.
Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

These passages were read directly. No source-specific errata directory was
present in the available Library. The sources give conventions and motivation;
this selected-index relative API and its functor are derived internal
constructions. The argument reuses `FiniteMonodromy` and `IntegralMonodromy`
and supplies their named geometric dependencies from
`FiniteEtale.geometricFiberFinite` and `AbelianScheme.torsionFiniteEtale`.
No new numerical rank or Galois-category theorem is needed.

## Actual objects and remaining hypotheses

All declarations are in `Langlands.AbelianScheme.Tate.Geometric`. Fix a scheme
`S`, an algebraically closed field `Ω` in the same universe, and a morphism
`s : Spec (.of Ω) ⟶ S`. `FundamentalGroup s` abbreviates exactly

```lean
FiniteEtale.FundamentalGroup s (FiniteEtale.geometricFiberFinite s)
```

with its existing evaluation topology. This is the automorphism group of the
actual finite geometric-fibre functor. No replacement group, carrier, or
topology is introduced. The imported group is compact, Hausdorff and totally
disconnected, and its operations are continuous. Connected locally noetherian
bases give the intended setting of the source's fundamental-group terminology;
the intrinsic evaluation constructions here apply to arbitrary `S` and assert
no classification theorem in greater generality.

`A : AbelianScheme S` is the actual bundled abelian scheme. At a finite level,
`n` must be positive and its image in `Γ(S, ⊤)` a unit. At selected integral
levels, a predicate `P : ℕ → Prop` and

```lean
hunit : ∀ n : GroupScheme.Tate.Index P, IsUnit (n.val : Γ(S, ⊤))
```

remain explicit. `Index P` already includes positivity. Fibre finiteness and
torsion finite étaleness are proved imported results, without supplied
comparison maps, bases, rank assumptions, or action data.

## Finite and integral representations

`levelRepresentation s A n hn hu` is a monoid homomorphism from
`FundamentalGroup s` to the linear automorphism group of the existing
`Level A (Over.mk s) n` over `ZMod n`. It bundles `levelMonodromy` and its
residue-scalar law. Its one and multiplication fields use the imported action
laws, with composition order

```text
ρ(g*h)(x) = ρ(g)(ρ(h)(x)).
```

`levelRepresentation_kernel` identifies it with component evaluation of
`g.hom.app` on the actual multiplication-kernel cover, transported through the
existing additive `kernelLevelEquiv`. `levelFinite` derives finiteness of this
actual torsion carrier from the two imported geometric results.
`continuous_levelRepresentation` is joint continuity for the existing group
topology and discrete level topology. `levelRepresentation_transition` and
`levelRepresentation_map` specialize the proved equivariance laws for the
existing divisibility transition and actual homomorphism-induced map.

`integralRepresentation s A P hunit` is the corresponding monoid homomorphism
into linear automorphisms of the existing `Integral A (Over.mk s) P` over
`Global.ProfiniteIntegerRing`. Its underlying equivalence is the published
`integralMonodromyLinearEquiv`; the group laws follow from the published
coordinate action laws. `evaluation_integralRepresentation` identifies every
coordinate with `levelRepresentation` on the same torsion section.
`continuous_integralRepresentation` specializes joint continuity for the
existing coherent-family subspace topology. No topology on the entire group
of linear automorphisms is asserted.

`integralAction` provides the same action as a locally installable
`DistribMulAction`, with the exact formula `integralAction_smul` and the
corresponding `integralAction_continuousSMul`. There is no global action instance.
`integralRepresentation_map` proves equivariance for every actual abelian-scheme
homomorphism, using the existing Tate map. None of these laws is assumed as
extra data.

## The profinite Tate-space functor

`integralCompactSpace` obtains compactness from actual selected-level
finiteness. `profiniteTate s A P hunit` bundles the existing integral carrier
and topology as a `Profinite` space, reusing `geometricProfiniteTate`.
Hausdorffness and total disconnectedness come from the existing topology module.

`profiniteTateMap s P hunit f` uses the published
`GroupScheme.Tate.profiniteMap` with the actual underlying group homomorphism
`AbelianScheme.groupHom f`. The finite-level instances needed for this
construction are derived from `levelFinite` for its source and target.
`profiniteTateMap_apply` identifies its function with the existing integral
Tate map. `evaluation_profiniteTateMap` gives its actual torsion coordinate.
`profiniteTateMap_id` and `profiniteTateMap_comp` follow by equality of functions
from the published `map_id` and `map_comp`. Thus `profiniteTateFunctor` is an
actual functor `AbelianScheme S ⥤ Profinite` for the fixed `s`, `P`, and `hunit`.
`profiniteTateMap_equivariant` records equivariance of its morphisms for the
constructed integral representations. The codomain of this functor is the
category of profinite spaces; its additive and scalar structure is supplied by
the existing Tate modules and representations, not additional categorical
structure on `Profinite`.

## Full and away specializations

`fullRepresentation` selects all positive orders and is linear over the full
profinite-integer ring. `awayRepresentation m` selects orders coprime to `m`
and is linear over `Global.PrimeToProfiniteIntegerRing m`, using the published
away scalar law. Its one and multiplication fields use the same coordinate
laws. `restrictAway_representation` proves that the existing full-to-away
restriction intertwines these representations; both sides have identical
coordinates. `fullProfiniteTateFunctor` and `awayProfiniteTateFunctor` specialize
the functor with the corresponding unit hypotheses.

For prime `m`, this is the prime-to-`m` construction. The predicate also permits
composite `m`, excludes precisely their prime divisors when `m` is nonzero,
selects only order one for `m = 0`, and selects all positive orders for `m = 1`.
No numerical rank, relative trivialization, compatible basis, rational or
adelic topology, pairing, pointed base change, or base-point independence is
asserted by this unit.
