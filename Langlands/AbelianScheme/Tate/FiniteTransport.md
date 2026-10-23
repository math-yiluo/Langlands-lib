# Finite torsion transport along an actual geometric path

Author: Worker 142.

This module evaluates an isomorphism of the actual finite geometric fibre
functors on finite étale group schemes and multiplication kernels. It constructs
additive transport on actual torsion levels, with compatibility under composition,
monodromy, torsion transitions, residue scalars, and scheme homomorphisms. Its
final interface specializes to the published bundled abelian schemes.

## Source and derived provenance

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary version built
2012-02-08, Chapter X §3, Definitions (10.25)–(10.26), printed p.150 / PDF p.154,
and (10.29), printed p.151 / PDF p.155, supplies the fibre-functor and change-of-
base-point conventions. Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
These passages were read in the original source extraction. The source permits
the two algebraically closed coefficient fields to differ and describes the
resulting isomorphism of fundamental groups as noncanonical. No corresponding
errata note was found in the available Library.

The Lean construction and its proofs are **derived** from naturality of an
actual given isomorphism of the published fibre functors. This is not a claim
that the source prints this precise API or proves the more general conditional
construction used here. In particular, existence of a path is not proved or
assumed implicitly. The finite étaleness theorem used by the abelian-scheme
specialization is the explicit named hypothesis documented in
`Langlands/AbelianScheme/TorsionFiniteEtaleStatement.md`.

## Inputs and scope

Fix a scheme `S` and field-valued points `s : Spec (.of Ω) ⟶ S` and
`t : Spec (.of Ω') ⟶ S`, with fields in the same universe. Each point comes
with the explicit finiteness hypothesis
`hs : ∀ Y : Cover S, Finite (Fiber s Y)` or its counterpart `ht`.
The path is exactly

```lean
p : fiberFunctor s hs ≅ fiberFunctor t ht
```

Both functors are the existing functors of actual finite étale covers and
actual points over `S`. A path is not an arbitrary isomorphism of torsion
modules or an unspecified group isomorphism. A third field and point are
allowed in the composition laws.

The geometric application takes the coefficient fields algebraically closed
and `S` connected and locally noetherian. Those conditions are not needed for
the conditional naturality arguments. The Lean declarations do not assert a
Galois-category theorem, path existence, or a geometric classification in their
absence. The generic finite-group transport permits a noncommutative group
object, using its points in additive notation; torsion-level transport uses a
commutative group object.

## Evaluation and conjugation

In `Langlands.AlgebraicGeometry.FiniteEtale`, `pathAct p Y x` is precisely
`p.hom.app (ofOver Y) x`. `pathAct_naturality` evaluates the naturality square
on a point. The category of covers is full, so every morphism between the
finite étale slice objects is available. `pathAct_lift` applies this to the
two product projections. `pathAct_one` uses the unit morphism and uniqueness
of a terminal-object point; `pathAct_mul` uses the multiplication morphism and
product preservation. Product and unit closure are the instances already
published in `FiniteMonodromy`.

`pathConjugation p` is Mathlib's `Aut.autMulEquivOfIso p`, on the existing
`FundamentalGroup` automorphism groups. On underlying functions it takes `g`
to `p ∘ g ∘ p⁻¹`. `continuous_pathConjugation` uses the existing inducing
embedding into the product of finite evaluation automorphism groups. At each
cover the map is conjugation by `p.app Y`; its source is discrete, so it is
continuous. The product criterion proves continuity, and applying the same
argument to `p.symm` proves inverse continuity.
`pathFundamentalGroupEquiv` bundles this as `≃ₜ*`, using the already published
evaluation topologies on both groups.

`groupPathTransport p G` bundles evaluation as an additive equivalence between
`Additive (Over.mk s ⟶ G.X)` and `Additive (Over.mk t ⟶ G.X)`. The reverse
path supplies its inverse. The inverse identities are the componentwise
identities of the natural isomorphism; additivity is `pathAct_mul`.
`groupPathTransport_refl` and `groupPathTransport_trans` give identity and
composition. `groupPathTransport_monodromy` gives equivariance with respect
to `pathConjugation p`, cancelling `p⁻¹ ∘ p` in the evaluation formula.

## Actual torsion levels

In `Langlands.GroupScheme.Tate`, the actual kernel of multiplication by `n`
is required to be finite and étale. With `e_s` and `e_t` denoting the existing
`kernelLevelEquiv` at the two points, `finiteLevelTransport G n p` is

```text
x ↦ e_t (groupPathTransport p (kernel (multiplication G n)) (e_s.symm x)).
```

`finiteLevelTransport_kernel` gives this formula on actual kernel points.
The `_refl`, `_trans`, and `_symm` lemmas identify transport for identity,
composed, and reverse paths. In particular, `p ≪≫ q` first transports by `p`
and then by `q`. `finiteLevelTransport_aut` identifies transport along a
loop with the existing `finiteLevelMonodromy`, rather than a new action.
`continuous_finiteLevelTransport` uses the existing discrete topology on
levels. The reverse path yields inverse continuity as well.
`finiteLevelTransport_zmod_smul` reduces a residue scalar to an integer
representative and uses preservation of integer scalar multiplication.

`finiteLevelTransport_monodromy` is equivariance under the conjugation
isomorphism. For two paths `p, q` from `s` to `t`,
`finiteLevelTransport_change_path` states that transport by `q` equals
transport by `p` followed by target-point monodromy for the loop
`p.symm ≪≫ q`. This gives the precise dependence on the path; it does not say
that transports by different paths are equal.

`finiteLevelTransport_transition` commutes with the existing `[m/n]` torsion
transition for `n ∣ m`. Both kernels must be finite étale. The proof writes a
level element as a kernel point, uses `kernelLevelEquiv_transition`, and
applies path naturality to the actual `kernelTransition` morphism.
`finiteLevelTransport_map` uses `kernelLevelEquiv_map` and path naturality
for `kernelLevelMap` in exactly the same way, for an actual group-scheme
homomorphism. The map is constructed from that homomorphism, not supplied as
an extra equivariant map.

## Abelian-scheme specialization

In `Langlands.AbelianScheme.Tate`, the main interface is

```lean
levelTransport htor A n hn hu p :
  Level A (Over.mk s) n ≃+ Level A (Over.mk t) n
```

Here `htor : TorsionFiniteEtaleStatement`, `hn : 0 < n`, and
`hu : IsUnit (n : Γ(S, ⊤))` remain explicit. The definition applies `htor`
to obtain the finite and étale properties of the actual multiplication kernel
on `A.toGrp`, and then specializes `finiteLevelTransport`. No unconditional
geometric instance or new torsion carrier is introduced.

`levelTransport_kernel` identifies evaluation at the published
`torsionCover htor A n hn hu`. The specialized laws are
`levelTransport_refl`, `levelTransport_trans`, `levelTransport_symm`,
`levelTransport_aut`, `continuous_levelTransport`,
`levelTransport_zmod_smul`, `levelTransport_monodromy`, and
`levelTransport_change_path`. They retain the same path order and monodromy
convention as the generic laws. The additive equivalence itself supplies
preservation of zero and addition.

`levelTransport_transition` explicitly requires positivity and invertibility
at both indices. `levelTransport_map` takes an actual abelian-scheme
homomorphism `f : A ⟶ B` and specializes the generic result using
`AbelianScheme.groupHom f`. The finite étaleness inputs are obtained locally
from the same `htor` for the relevant abelian schemes and orders.

This focused unit does not construct transport on integral or rational Tate
limits, pointed base change, pairings, or invariant level orbits. It supplies
the finite-level difference-of-path formula needed for later independence
of a fixed-orbit set; it does not yet claim that independence or a canonical
unpointed functor.
