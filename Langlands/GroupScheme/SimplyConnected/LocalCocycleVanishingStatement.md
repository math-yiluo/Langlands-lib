# Local vanishing for simply connected group-scheme cocycles

Authors: Worker 1757.

`Langlands.GroupScheme.LocalSimplyConnectedCocycleVanishingStatement.{u}` is
a proposition definition, at arbitrary universe `u`. This module states it
and supplies no proof.

## Exact statement and actual cocycles

Let `F : Type u` have instances `[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`. Let `G` be an actual
group scheme over `Spec F`, with `[IsAffineHom G.X.hom]` and
`IsSimplyConnected G`. The latter predicate includes `IsSemisimple G` and
algebraic simple connectedness; it is not a topological condition.

For every field `L : Type u` with `[Algebra F L] [FiniteDimensional F L]
[Algebra.IsSeparable F L]`, set

```
U = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L))).
```

For every actual `ξ : Cocycle G U`, the conclusion is `ξ.IsTrivial`.
No valuation or topology on `L` is an input. The field extension is finite
separable and need not be Galois.

Here the imported `Cocycle` is a natural family of group points: for every
test scheme `Z` over `Spec F` and every `a b : Z ⟶ U`, it gives a morphism
`ξ.toFun a b : Z ⟶ G.X`, compatibly with pullback and satisfying
`ξ.toFun a c = ξ.toFun a b * ξ.toFun b c`. The conclusion means that there
exists an actual morphism `f : U ⟶ G.X` such that, for all tests and all such
`a b`,

```
ξ.toFun a b = (a ≫ f) * (b ≫ f)⁻¹.
```

These are all the hypotheses and data. The statement covers positive
characteristic and anisotropic groups, and does not impose almost simplicity,
absolute simplicity, a splitting, or a quasi-splitting condition.

## Source and derived formulation

G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem*, Comment.
Math. Helv. 60 (1985), 107–121, registered as
`prasad-raghunathan-1985-kneser-tits`, §2, printed p. 111 / PDF p. 6 of the
retained copy, recalls vanishing of first Galois cohomology for connected
semisimple simply connected groups over nonarchimedean local fields.
It attributes the characteristic-zero result to Kneser and the
arbitrary-characteristic result to Bruhat–Tits.

The present statement is the finite-separable Čech consequence of that
vanishing, written with the Library's existing scheme-valued cocycles.
The conceptual passage uses effective descent of the trivial group torsor on
the finite étale faithfully flat cover `Spec L → Spec F`: a cocycle gives a
torsor, and triviality of its cohomology class gives a coboundary on the same
cover. This explains the provenance of the formulation. This module supplies
neither that comparison as a Lean theorem nor a proof of the local vanishing.
It does not define a Galois cohomology object or identify two cohomology
objects by definition.

## Consumer and retained obligations

Local cohomology vanishing is a substantial arithmetic input to the
Prasad–Raghunathan local rank-one reduction used for the proof task targeting
`LocalKneserTitsStatement`. Proving this cocycle statement alone does not
establish that target. The required cohomological exactness and kernel
comparison in their Theorem B, rational generation by rank-one groups,
classification over local fields, and generation for the resulting classical
forms remain separate obligations.
