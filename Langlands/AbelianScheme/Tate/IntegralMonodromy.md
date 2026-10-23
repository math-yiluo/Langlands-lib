# Geometric monodromy on actual integral Tate limits

Author: Worker 142.

This module constructs the continuous action of the actual finite geometric-fibre
functor's automorphism group on the existing integral Tate limit of an abelian
scheme. It proves compatibility with the full and away residue scalar actions,
with actual homomorphisms, and with full-to-away restriction. Compactness follows
from the same finite-level geometric hypotheses used to construct the action.

## Sources and derived provenance

- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), Chapter I, printed p.18 / PDF p.26, and Section III.1, printed
  pp.91–92 / PDF pp.99–100. Registered source:
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  Page 18 defines the full Tate limit over all positive integers and the away
  limit over integers coprime to a finite set of primes. Pages 91–92 use
  geometric monodromy on rational Tate fibres to specify invariant orbits.
- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary version built
  2012-02-08, Chapter X §3, Definitions (10.25)–(10.26), printed p.150 /
  PDF p.154. Registered source:
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  These definitions specify finite étale covers, the geometric-fibre functor,
  and its automorphism group.

The source passages were read directly. No source-specific errata directory
was present in the available Library. This module is a **derived** extension
of the imported finite-level geometric action to coherent families. Neither
source is claimed to contain this exact generalized API or its Lean proof.
The selected-index formulation and the conditional scope below are internal
generalizations. The cited rational invariant-orbit constructions motivate
this integral prerequisite; this module does not yet construct those orbits.

## Actual objects and hypotheses

All declarations lie in `Langlands.AbelianScheme.Tate`. Fix a scheme `S`, a
field `Ω`, a field-valued point `s : Spec (.of Ω) ⟶ S`, and an actual bundled
abelian scheme `A : AbelianScheme S`. The group acting is exactly the existing
`FiniteEtale.FundamentalGroup s hfin`, the natural automorphism group of the
actual finite-fibre functor, with its existing evaluation topology.

The following explicit hypotheses remain:

```lean
hfin : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber s Y)
htor : Langlands.AbelianScheme.TorsionFiniteEtaleStatement
hu : ∀ n : GroupScheme.Tate.Index P, IsUnit (n.val : Γ(S, ⊤))
```

Here `Index P` consists of the positive natural numbers satisfying `P`.
`hfin` and `htor` are named theorem dependencies, not properties hidden in a
new geometric structure or unconditional instances. The imported
`levelMonodromy` uses the actual multiplication kernel at each selected order,
its finite étaleness provided by `htor`, and the kernel-point equivalence with
`Level A (Over.mk s) n.val`. Thus the resulting limit action is tied to actual
geometric evaluation, rather than an arbitrary supplied family of actions.

The carrier `Integral A (Over.mk s) P` is the already constructed subgroup of
coherent families in the product of these torsion levels. Its coherence uses
the existing transition `[m/n]` for `n ∣ m`; its topology is the existing
product-subspace topology, with each torsion level discrete. No new carrier,
transition system, or topology is introduced here.

The intended geometric setting has `Ω` algebraically closed and `S` connected
and locally noetherian. The conditional inverse-limit argument needs no such
extra assumptions once the displayed hypotheses are supplied. It asserts no
geometric classification theorem outside that setting. In the full case all
positive orders must be invertible on `S`; in the away case only retained
orders must be invertible. The characteristic-zero application meets the full
invertibility requirement; the module retains it explicitly.

## Construction and action laws

`integralMonodromyHom s hfin htor A P hu g` applies the imported
`levelMonodromy ... g` to every coordinate. The existing universal `lift`
constructs its value as a coherent family. Coherence follows from
`levelMonodromy_transition` and the input family's coherence law.
`evaluation_integralMonodromyHom` identifies each coordinate definitionally.

`integralMonodromyHom_one` and `integralMonodromyHom_mul` prove, by equality in
every coordinate, respectively

```text
ρ(1)(x) = x,             ρ(g*h)(x) = ρ(g)(ρ(h)(x)).
```

`integralMonodromy` bundles this map as an additive automorphism; its inverse
is `integralMonodromyHom ... g⁻¹`. The inverse identities follow from the two
action laws. `integralMonodromy_apply` identifies its function with the
homomorphism just constructed. `integralMonodromyAction` is a locally
installable `DistribMulAction`, using the same function and additive laws.
It installs no global action. The explicit multiplication formula above avoids
confusing the multiplicative acting group with Mathlib's additive composition
convention for `AddAut`.

## Continuity and compactness

`continuous_integralMonodromy_coordinate` composes finite-level joint
continuity with the continuous map `(g,x) ↦ (g,evaluation n x)`.
`continuous_integralMonodromyHom` applies the published
`GroupScheme.Tate.continuous_iff_evaluation` criterion and the coordinate
formula. `continuous_integralMonodromy` transfers this result through
`integralMonodromy_apply`. `integralMonodromyAction_continuousSMul` packages
joint continuity for exactly the locally installed action above. The group
and Tate topologies in all these results are the existing ones.

`integralMonodromy_compactSpace` derives finiteness at each selected level from
`level_finite s hfin htor A ...`, then uses the published compactness instance
for the coherent-family Tate limit. No separate finite-level cardinality or
rank hypothesis is supplied. `geometricProfiniteTate` bundles that same Tate
space as `Profinite`; Hausdorffness and total disconnectedness come from the
published topology module. This asserts compactness of the Tate carrier, not
a new theorem about the fundamental group or a Galois-category equivalence.

## Scalars, naturality, and full/away forms

`integralMonodromy_full_smul` proves that the action commutes with the existing
`Global.ProfiniteIntegerRing` action, for every predicate `P`. The proof is
coordinatewise: the profinite scalar acts at order `n` through
`GroupScheme.Tate.fullReduction P n`, and the finite action preserves the
`ZMod n.val` scalar multiplication. `integralMonodromyLinearEquiv` bundles the
same additive automorphism as a linear equivalence over this full residue
ring. No finite-adele scalar comparison is used.

For an actual abelian-scheme homomorphism `f : A ⟶ B`,
`integralMonodromy_map` proves equivariance of the existing `map (Over.mk s) P f`.
The proof is equality in each coordinate using `levelMonodromy_map`.
Equivariance of `f` is thus derived from geometric naturality; it is not an
extra assumption on `f`.

`fullMonodromy` specializes to `P(n) = True`. `awayMonodromy m` specializes to
`P(n) = Nat.Coprime n m`. For a prime `m` this is the prime-to-`m` action; for
nonzero composite `m` it excludes its prime divisors. The formal case `m = 0`
is also allowed by the predicate, without a claim that it is the usual
prime-to-a-prime setting. The selected continuity and compactness results
specialize to both aliases with their corresponding invertibility hypotheses.

`awayMonodromy_smul` proves compatibility with the existing
`Global.PrimeToProfiniteIntegerRing m` action using `awayReduction` in each
coordinate. `awayMonodromyLinearEquiv` gives the corresponding linear
equivalence. Finally, `restrictAway_monodromy` states that the existing
full-to-away map intertwines the full action and the action with the restricted
invertibility evidence. Both sides read the same selected coordinates, so its
proof is definitional equality.

Rational and adelic monodromy, prime-power comparison compatibility, pairings,
pointed base change, and independence from the base point are subsequent
obligations. This unit proves none of the still-explicit geometric hypotheses.
