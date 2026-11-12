# Transport of the Hecke induction functors to smooth representations

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.2.1, printed p.70 / PDF p.76, using
the equivalence of III.1.4, printed p.60 / PDF p.66, and the functors of
I.2.3, printed pp.17–18 / PDF pp.23–24. Source ID:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

For a continuous homomorphism `φ : H →* G`, `restriction` names the
published general smooth pullback functor
`Langlands.MixedProductTensor.pullbackFunctor φ hφ`. It sends an action
`π` to `h ↦ π(φ(h))` and keeps its carrier and morphism maps.
This is (III.2.1.1). The published `SmoothRep.pullback` is the
group-equivalence specialization, so it cannot itself be applied to an
arbitrary continuous homomorphism.

`smoothF`, `smoothPseudoF`, `smoothI` and `smoothP` transport the
four actual Hecke-module functors through the published
`heckeNondegenerateModuleFunctor` and its categorical inverse. For example,

`smoothI = HeckeH ⋙ Homomorphism.I ⋙ HeckeG.inv`.

The constructors explicitly take the needed proof that the exact published
Hecke functor is an equivalence. This is the proposition asserted by the
published `HeckeNondegenerateModuleEquivalenceStatement` (III.1.4);
its proof is not supplied or assumed globally by this file. An equivalence
of unrelated categories cannot replace this input, and no new module
category or alternative Hecke correspondence is introduced.

The definitions apply to Hausdorff locally compact nonarchimedean groups
with supplied left Haar measures. Both group universes `uG`, `uH`
and the free carrier universe `v` are independent. To compose a functor
with its adjoint at a single category size, these transported functors use
carrier universe `max uG v`, which is stable under the existing
tensor and Hom constructions. There is no inequality imposed on `uH`.
The underlying Hecke functors remain available on any input carrier universe,
with their original output universe `max uG v`.

This file only constructs transport functors. In particular, it does not
assert that the equivalence inputs exist, that `restriction` and `smoothF`
are naturally isomorphic, or that any functors here are adjoint. Those are
separate closed proposition targets.
