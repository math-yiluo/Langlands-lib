# Geometric path transport on finite roots of unity

This internal construction transports actual roots of unity along a given
isomorphism of the finite geometric fibre functors. It specializes the
published `GroupScheme.Tate.finiteLevelTransport` to the multiplicative
group and uses the affine comparison from `TwistFiniteMonodromy`. All
new public declarations belong to `Langlands.TateTwist.Geometry`.

## Inputs and existing carriers

Fix a scheme `S`, fields `Ω`, `Ω'`, and, for composition, `Ω''` in the
same universe, and points `s : Spec Ω ⟶ S`, `t : Spec Ω' ⟶ S`, and
`r : Spec Ω'' ⟶ S`. Each used point has an explicit hypothesis such as
`hs : ∀ Y : Cover S, Finite (Fiber s Y)`. A path is exactly a supplied
natural isomorphism

```text
γ : fiberFunctor s hs ≅ fiberFunctor t ht.
```

The fibre functors are the existing functors of actual finite étale
covers and their points over `S`. The construction assumes no field map
between `Ω` and `Ω'`. It asserts neither existence of such a path nor an
identification with a field Galois group. Algebraic closure, connectedness
and local noetherianity are not needed for these conditional constructions.

For a natural number `n`, require that the structural morphism of the
actual scheme `mu S n` is finite and étale. These are explicit instance
hypotheses. No positivity restriction is imposed by this conditional API;
in particular it does not assert that these hypotheses hold at `n = 0`.
The source and target are the existing `TateTwist.Level Ω n` and
`TateTwist.Level Ω' n`: the additive forms of actual groups of roots of
unity, with their published residue module structures and discrete
topologies.

The two private kernel lemmas merely expose the definitional equality
between `mu S n` and the multiplication kernel on `Gm S` to instance
search. They introduce no new geometric finite-etaleness result.

## Transport and its geometric formula

Let `e_s = Gm.TateComparison.affineLevelEquiv s n` and similarly `e_t`.
The additive equivalence `levelTransport n γ` is

```text
x ↦ e_t (GroupScheme.Tate.finiteLevelTransport (Gm S).toGrp n γ (e_s.symm x)).
```

This is the existing geometric evaluation on the actual multiplication
kernel, carried through the published affine torsion-to-roots equivalences.
`affineLevelEquiv_transport` expresses this compatibility explicitly by
cancelling `e_s.symm ∘ e_s`.

`levelTransport_kernel` identifies the map on actual kernel points:

```text
levelTransport n γ (mu.levelEquiv n s x)
  = mu.levelEquiv n t (Additive.ofMul (pathAct γ (mu S n).X x.toMul)).
```

Here `pathAct γ` is exactly evaluation of `γ.hom` on the cover. The proof
uses the published kernel formulas for the affine comparison and finite
transport. Thus the construction does not replace path evaluation with an
arbitrary isomorphism between root groups.

## Identity, composition, inverse, and linearity

`levelTransport_refl` states that the identity path acts identically.
`levelTransport_trans` states that `γ ≪≫ δ` first transports by `γ` and
then by `δ`. Both follow by cancelling the intermediate affine equivalence
and using the corresponding finite torsion transport laws.
`levelTransport_symm` identifies the inverse equivalence with transport
along the reverse path by reflexivity.

For `g : FundamentalGroup s hs`, `levelTransport_aut` identifies transport
along this loop with the existing `levelMonodromy s hs n g`, also by
reflexivity. The construction therefore extends the previously published
geometric root action with the same convention.

`levelTransportLinear` bundles transport as a `ZMod n`-linear equivalence.
Its scalar law follows from `ZMod.map_smul` for the underlying additive
homomorphism on the existing residue modules.
`continuous_levelTransport` follows from the existing discrete source
topology. `levelTransportContinuousLinearEquiv` bundles this linear map
and continuity in both directions, using the same result for `γ.symm`.
No topology on the space of paths is introduced or used.

## Monodromy and dependence on the path

`levelTransport_monodromy` states

```text
T_γ(ρ_s(g)(x)) = ρ_t(pathConjugation γ g)(T_γ(x)).
```

The group isomorphism is exactly the published `pathConjugation γ`.
On underlying functions it is `g ↦ γ ∘ g ∘ γ⁻¹`. The proof unfolds
transport and monodromy through the same affine equivalences, cancels the
inverse comparisons, and invokes `finiteLevelTransport_monodromy`.

For two paths `γ, δ` from `s` to `t`, `levelTransport_change_path` states

```text
T_δ(x) = ρ_t(γ.symm ≪≫ δ)(T_γ(x)).
```

The loop here is at the target point. The proof rewrites its monodromy as
transport, applies the composition law, and cancels `γ ≪≫ γ.symm`.
It states the precise dependence on a path; it does not assert that two
path transports are equal.

## Divisibility transitions and scope

For `h : n ∣ m`, with explicit finite étaleness at both orders,
`levelTransport_transition` proves

```text
T_γ,n(transition Ω h x) = transition Ω' h (T_γ,m(x)).
```

These are the existing quotient-power transitions on roots of unity.
The proof represents `x` through the surjective affine comparison,
rewrites both transitions using `affineLevelEquiv_transition`, and applies
the published finite torsion transition law.

The provenance is internal: this module derives its constructions and
proofs from the published `FiniteTransport` and `TwistFiniteMonodromy`
APIs. No new statement is attributed to external literature. No roots,
basis or trivialization are chosen. Transport on integral or rational
limits, pointed base change, pairing compatibility and independence of
PEL invariant-orbit level structures remain separate work.
