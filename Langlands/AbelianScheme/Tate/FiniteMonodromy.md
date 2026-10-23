# Geometric monodromy on finite torsion fibres

Author: Worker 155.

This module constructs the action of the actual finite geometric-fibre functor's
natural automorphisms on the existing torsion levels of an actual abelian scheme.
It proves the intrinsic action, continuity, scalar, and equivariance laws needed
to extend that action to Tate limits. The finite-level objects, maps, topology,
and acting group are the published constructions, rather than supplied action
data.

## Sources and derived provenance

The following originals were read directly:

- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), Chapter I, printed p.18 / PDF p.26, and Section III.1, printed p.91 /
  PDF p.99. Registered source:
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  The first location fixes the torsion-limit conventions; the second uses
  geometric monodromy in the invariant-orbit description of level structures.
- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary version built
  2012-02-08, Chapter X §3, Definitions (10.25)–(10.26), printed p.150 /
  PDF p.154. Registered source:
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  These definitions give the actual category of finite étale covers, its
  geometric point functor, and the fundamental group as its automorphism group.

The construction and all transport proofs here are **derived** from these
conventions and the imported Library definitions. Neither source is claimed to
print this exact generalized Lean API or the proofs below. The geometric torsion
theorem is an explicit hypothesis with its source correspondence documented in
`Langlands/AbelianScheme/TorsionFiniteEtaleStatement.md`. This module does not
prove that theorem. No source-specific errata note was found in the available
Library when the sources were read.

## Hypotheses and generality

The generic declarations use a scheme `S : Scheme.{u}`, a field `Ω : Type u`,
and a morphism `s : Spec (.of Ω) ⟶ S`. They retain the explicit named hypothesis

```lean
hfin : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber s Y)
```

which is the content of the published `GeometricFiberFinite` target in its
geometric setting. The acting group is exactly
`FiniteEtale.FundamentalGroup s hfin = Aut (FiniteEtale.fiberFunctor s hfin)`.
Its existing evaluation topology and the existing discrete fibre topologies
are used. No arbitrary group or action is an input.

The intended source setting takes `Ω` algebraically closed and `S` connected
and locally noetherian. None of these extra hypotheses is needed for the
conditional evaluation and transport arguments implemented here. Without them,
these names refer to the same formal automorphism construction; this module
asserts no stronger geometric classification theorem. The generic action on
finite étale group schemes even permits noncommutative group objects. The
kernel-level construction uses commutative group objects, and the final
specialization uses the published bundled `AbelianScheme`.

For every selected abelian-scheme level the specialization explicitly takes
`htor : Langlands.AbelianScheme.TorsionFiniteEtaleStatement`, `hn : 0 < n`,
and `hu : IsUnit (n : Γ(S, ⊤))`. In transition compatibility these conditions
are required at both indices. `hfin` and `htor` are theorem dependencies, not
additional fields of a geometric object and not unproved global instances.

## Evaluation preserves the group structure

The first namespace is `Langlands.AlgebraicGeometry.FiniteEtale`.
`ofOver Y` packages an actual slice object whose structural map is finite and
étale. `act s hfin Y g x` is exactly `g.hom.app (ofOver Y) x` on an actual
slice morphism `x : Over.mk s ⟶ Y`. `act_naturality` specializes the published
`smul_naturality` to any slice morphism between such objects, using fullness of
the finite étale category.

`tensor_isFinite` and `tensor_etale` prove closure for the Cartesian product
in the slice: its structure map is a scheme pullback projection followed by
the original structure map. Mathlib's base-change and composition instances
prove the two properties. `unit_isFinite` and `unit_etale` reduce to the
identity of `S`. No product or unit closure is assumed as extra data.

`act_lift` proves preservation of a pair of points by applying naturality to
both projections and using the product's uniqueness property. `act_one` then
uses naturality of the group unit and uniqueness of the point of the terminal
object. `act_mul` uses `act_lift` and naturality of the actual multiplication
morphism. Thus the pointwise group operations are preserved by evaluation.

`groupMonodromy s hfin G g` bundles evaluation as an
`AddAut (Additive (Over.mk s ⟶ G.X))`. Its inverse is evaluation at `g⁻¹`;
the inverse laws are the componentwise inverse identities of the natural
isomorphism. Additivity is `act_mul` in additive notation. The identity and
composition laws are `groupMonodromy_one` and `groupMonodromy_mul`.
`groupAction` packages these as a locally installable `DistribMulAction`.
Mathlib's `AddAut` uses an additive composition-group convention, so the API
states the multiplicative acting-group law explicitly rather than presenting
an ordinary multiplicative homomorphism into `AddAut`.

`continuous_groupMonodromy` reuses the published joint continuity of fibre
evaluation. Its type explicitly specifies the existing fibre topology after
the additive type tag; it installs no new global topology on section types.
`groupMonodromy_naturality` proves equivariance for an actual group-scheme
homomorphism by `act_naturality`.

## Actual kernel maps and transport

The second namespace is `Langlands.GroupScheme.Tate`. Fix a commutative group
scheme `G`. The existing `kernelLevelEquiv G T n` is an additive equivalence
from points of the actual multiplication kernel to the existing `Level G T n`.

`kernelLift` applies its inverse to a torsion section. `kernelLift_ι` says
that composing with the actual kernel inclusion recovers that section.
`kernelSection` is the image of the identity morphism of the kernel under
the equivalence, and `kernelSection_val` identifies it with the kernel inclusion.

For `h : n ∣ m`, `kernelTransition G h` lifts the image of the universal
`m`-torsion section under the **existing** `transition G _ h` to the actual
`n`-multiplication kernel. `kernelTransition_ι` identifies its composite with
the target inclusion with the source inclusion followed by the actual
multiplication morphism `[m/n]`. `kernelLevelEquiv_transition` proves, on every
test scheme, that postcomposition with this morphism is exactly the existing
transition. The proof uses injectivity into sections, associativity, the
inclusion formula, and `points_multiplication`.

Likewise, for an actual group-scheme homomorphism `f : G ⟶ H`,
`kernelLevelMap f n` is constructed by lifting the image of the universal
kernel section under the **existing** `levelMap`. `kernelLevelMap_ι` gives
its inclusion formula. `kernelLevelEquiv_map` identifies its point map with
that existing `levelMap`, again by injectivity into sections. These helpers
are slice morphisms; fullness of the finite étale category is sufficient for
the subsequent naturality arguments.

When the actual multiplication kernel at `n` has finite étale structural map,
`finiteLevelMonodromy G s hfin n g` transports `groupMonodromy` through
`kernelLevelEquiv`. Concretely, writing that equivalence as `e`, the action is
`x ↦ e (groupMonodromy s hfin (kernel (multiplication G n)) g (e.symm x))`.
`finiteLevelMonodromy_kernel` records the evaluation formula on kernel points.
The one and multiplication laws cancel the inverse equivalence.

`finiteLevel_finite` transports `hfin` for that particular kernel cover through
the same equivalence. It assumes no finiteness of `Level` separately.
`continuous_finiteLevelMonodromy` proves joint continuity by composing the
already continuous fibre evaluation with the equivalence and its inverse;
both equivalence maps are continuous because their source topologies are
discrete. The target level topology is the one published in `Tate.Integral`.

`finiteLevelMonodromy_zmod_smul` uses the `ZMod n` module structure already
published in `Tate.PrimeAdic`. An integer representative of the residue scalar
reduces the result to preservation of integer scalar multiplication by an
additive homomorphism. Finally, `finiteLevelMonodromy_transition` and
`finiteLevelMonodromy_map` use the two kernel point formulas and naturality of
evaluation. The generic statements require the relevant kernels to be finite
and étale; they do not assert such geometric properties for arbitrary indices.

## Abelian-scheme interface

The final namespace is `Langlands.AbelianScheme.Tate`.
`torsionCover htor A n hn hu` is the actual kernel of multiplication by `n` on
`A.toGrp`, packaged using exactly the two conclusions of `htor S A n hn hu`.
`torsionKernel_isFinite` and `torsionKernel_etale` expose those conclusions with
the actual kernel type. The wrappers use them locally as typeclass evidence.
They are proved theorems taking `htor`, not unconditional instances.

The main interface is

```lean
levelMonodromy s hfin htor A n hn hu g : AddAut (Level A (Over.mk s) n)
```

It specializes the generic transport, with the published `AbelianScheme.Tate`
level and kernel equivalence. `levelMonodromy_kernel` gives forward transport
of evaluation at `torsionCover`; `kernelPoint_levelMonodromy` gives the reverse
formula on underlying kernel points. Thus the level action is explicitly tied
to evaluation by the actual natural automorphism `g`.

The exported intrinsic laws are `levelMonodromy_one`, `levelMonodromy_mul`,
`levelMonodromy_zero`, `levelMonodromy_add`, and `levelMonodromy_zmod_smul`.
`levelAction` packages the action as a locally installable `DistribMulAction`.
`level_finite` retains all of `hfin`, `htor`, `hn`, and `hu` in its signature
and derives finiteness through the kernel equivalence.
`continuous_levelMonodromy` gives joint continuity with the existing level
topology. `levelAction_continuousSMul` gives `ContinuousSMul` with this
particular `levelAction` installed locally in its statement.

`levelMonodromy_transition` states equivariance of the published
`transition A (Over.mk s) h` for `h : n ∣ m` at two positive invertible levels.
`levelMonodromy_map` states equivariance of the published
`levelMap (Over.mk s) f n` for an actual abelian-scheme homomorphism `f : A ⟶ B`.
It passes `AbelianScheme.groupHom f` to the generic result. Neither theorem
takes an equivariant map as an extra hypothesis.

This unit preserves the original statement targets. It constructs no action
on an integral or rational Tate limit, rational topology, pairing, base-point
transport, or Galois-category equivalence. Those are separate extensions.
