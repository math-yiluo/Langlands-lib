# Geometric path transport on rational roots-of-unity twists

This internal construction extends the published integral geometric root
transport from integers to rationals. It imports `TwistIntegralTransport`
and `TwistRationalMonodromy`; every new declaration is in
`Langlands.TateTwist.Geometry`.

## Inputs and existing carriers

Fix a scheme `S`, fields `Ω`, `Ω'`, and, for composition, `Ω''` in the
same universe, and points `s : Spec Ω ⟶ S`, `t : Spec Ω' ⟶ S`,
`r : Spec Ω'' ⟶ S`. For each used point, an explicit hypothesis such
as `hs : ∀ Y : Cover S, Finite (Fiber s Y)` says that all actual
finite étale covers have finite fibres at that point. A path is a supplied
natural isomorphism `γ : fiberFunctor s hs ≅ fiberFunctor t ht`.

For `P : ℕ → Prop`, `Index P` consists of the positive integers satisfying
`P`. Instance families `hμfin` and `hμet` require the structural morphism
of the actual roots-of-unity scheme `mu S n.val` to be finite and étale
at every such index. No theorem deriving these hypotheses from invertibility
of the orders is asserted here. No algebraic closure or connectedness
hypothesis is needed for this conditional construction, and no existence
of a path is proved.

The source and target are the existing
`Divisibility.Rational Ω P = ℚ ⊗[ℤ] Divisibility.Integral Ω P`
and the corresponding module for `Ω'`. Their integral factors are the
coherent families of actual roots of unity for the quotient-power
transitions. The construction chooses no field map, roots, basis or
trivialization of the twist.

## Scalar extension and path laws

`rationalTransportMap P γ` is the `ℚ`-linear scalar extension of
`integralTransportHom P γ`, first viewed as a `ℤ`-linear map.
Its pure-tensor formula, `rationalTransportMap_tmul`, is

```text
q ⊗ x ↦ q ⊗ integralTransport P γ x.
```

Thus the integral factor still comes from evaluation of the same path
on the actual roots-of-unity covers.
`rationalTransportMap_refl` proves the identity law by tensor induction,
using the integral identity law on pure tensors and additivity.
`rationalTransportMap_trans` uses the same induction and the integral
composition law. Its convention is

```text
T_(γ ≪≫ δ)(x) = T_δ(T_γ(x)).
```

`rationalTransport P γ` bundles a `ℚ`-linear equivalence with inverse
the map for `γ.symm`. The inverse equations follow from composition,
path cancellation and identity. `rationalTransport_tmul`,
`rationalTransport_refl`, `rationalTransport_trans`, and
`rationalTransport_symm` retain the pure-tensor, identity, composition
and inverse formulas for the bundled equivalence.

`toRational_transport` states that the existing canonical map
`Divisibility.toRational`, given by `x ↦ 1 ⊗ x`, commutes with transport.
Its proof is reflexivity. It asserts no injectivity of that canonical map.

## Monodromy and dependence on the path

For `g : FundamentalGroup s hs`, `rationalTransport_aut` identifies the
entire linear equivalence with the published `rationalMonodromy s hs P g`.
Tensor induction reduces this to `integralTransport_aut` on pure tensors.
Both monodromy and transport are therefore derived from the actual
geometric finite-fibre functor.

`rationalTransport_monodromy` proves

```text
T_γ(ρ_s(g)(x)) = ρ_t(pathConjugation γ g)(T_γ(x)).
```

The proof uses tensor induction and the integral conjugation identity
on the integral factor. The group isomorphism `pathConjugation γ`
is the existing geometric conjugation induced by the same path.

For two paths `γ, δ` from `s` to `t`,
`rationalTransport_change_path` proves

```text
T_δ(x) = ρ_t(γ.symm ≪≫ δ)(T_γ(x)).
```

The displayed loop is at the target point. The proof rewrites its
monodromy as transport, applies composition and cancels the reverse path.
This records the precise dependence on the path; it does not prove
equality of arbitrary transports or independence of PEL fixed-orbit sets.

## Full residue and finite-adelic scalars

`rationalTransport_scalarAction` states that transport commutes with the
existing action of `ℚ ⊗[ℤ] Global.ProfiniteIntegerRing` on both rational
twists. It applies `TateScalarExtension.map_action` to the actual
`integralTransportLinearEquiv`, whose scalar action is the published
coordinate residue action.

Given an explicit
`h : Global.RationalProfiniteIntegerAdeleComparison`,
`rationalTransport_finiteAdeleAction` transfers this scalar law to the
existing action of `Global.FiniteAdeles ℚ`. `finiteAdeleTransport` bundles
the same equivalence as linear over that ring, with the two local module
instances `Divisibility.finiteAdeleModule Ω P h` and its target counterpart.
`finiteAdeleTransport_apply` states that its underlying function is
exactly `rationalTransport`. The comparison `h` remains an input; no new
finite-adele comparison theorem is proved by this construction.

## Full and away specializations

`rationalFullTransport` specializes to `P = True`, requiring finite
étaleness at all positive orders. `rationalAwayTransport m` specializes
to `P n = Nat.Coprime n m`, requiring it only at those retained orders.
Here `m` is any natural number. The selected path and monodromy laws apply
to these abbreviations directly.

`rationalRestrictAway_transport` states

```text
rationalRestrictAway Ω' m (rationalFullTransport γ x)
  = rationalAwayTransport m γ (rationalRestrictAway Ω m x).
```

The theorem takes the full finite étale families explicitly and restricts
those exact families to the away indices for its target transport.
Tensor induction proves the equality: on pure tensors the integral
coordinate maps agree by reflexivity, and additivity handles sums.

`rationalAwayTransport_scalarAction` commutes with the additional existing
action of `ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m`. This applies
`TateScalarExtension.map_action` to `awayTransportLinearEquiv`, rather than
asserting a new scalar action. Given explicit comparisons `h` and
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`,
`rationalAwayTransport_primeToFiniteAdeleAction` transfers that equality
to the existing action of `Global.PrimeToFiniteAdeles m`.
`primeToFiniteAdeleTransport` packages the same equivalence over this
ring using the existing local modules at both fields.
`primeToFiniteAdeleTransport_apply` records equality of its underlying
function with `rationalAwayTransport`.

## Provenance and scope

The construction is internally derived from the published integral root
transport, rational root carriers, geometric monodromy and scalar-extension
action law. The proof route is described above. It parallels the published
abelian-scheme `RationalTransport` pattern, with the actual roots-of-unity
carriers and hypotheses; no new assertion is attributed to literature.

This is algebraic rational transport. It introduces no rational topology
or continuity claim. Prime-adic rational transport, pointed base change,
pairing compatibility, path existence and canonical PEL fixed-orbit
independence remain separate work. It neither proves a restricted-product
comparison nor claims completion of the parent PEL infrastructure task.
