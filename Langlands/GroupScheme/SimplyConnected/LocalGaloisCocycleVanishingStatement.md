# Local vanishing for simply connected cocycles on finite Galois covers

Authors: Worker 1545.

`Langlands.GroupScheme.LocalSimplyConnectedGaloisCocycleVanishingStatement.{u}`
is a proposition definition at arbitrary universe `u`. This module states it
and proves nothing.

## Exact statement

Let `F : Type u` have the instances `[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`. Let `G` be an actual
group scheme over `Spec F` with `[IsAffineHom G.X.hom]` and
`IsSimplyConnected G`. The imported predicate `IsSimplyConnected` includes
`IsSemisimple G` and algebraic simple connectedness. It is not a topological
condition.

Take any field `M : Type u` with `[Algebra F M] [FiniteDimensional F M]
[IsGalois F M]`, and set

```
U = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F M))).
```

The conclusion is that every actual `ξ : Cocycle G U` satisfies
`ξ.IsTrivial`. As in the imported `Langlands.GroupScheme.TorsorCocycle`,
`ξ` is a natural family of group points `ξ.toFun a b : Z ⟶ G.X`. It is
defined for every test scheme `Z` over `Spec F` and all `a b : Z ⟶ U`, and
satisfies `ξ.toFun a c = ξ.toFun a b * ξ.toFun b c`. Triviality means that
some actual `f : U ⟶ G.X` satisfies `ξ.toFun a b = (a ≫ f) * (b ≫ f)⁻¹` for
every test and every such `a b`.

The statement makes no restriction on the characteristic of `F` and no
isotropy, almost-simplicity, absolute-simplicity, splitness or
quasi-splitness assumption on `G`. No valuation or topology on `M` is an
input.

## Relation to the separable-cover statement

This proposition is the published
`Langlands.GroupScheme.LocalSimplyConnectedCocycleVanishingStatement.{u}`
with one change: the hypothesis `[Algebra.IsSeparable F L]` on the cover
field is replaced by `[IsGalois F M]`. Every other binder and the conclusion
are unchanged. The companion module
`Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingGaloisReduction`
proves in Lean that the two propositions are equivalent, as
`localSimplyConnectedGaloisCocycleVanishing_iff`. This module itself
proves no such comparison.

## Source and derived formulation

Provenance: derived.

G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem*, Comment.
Math. Helv. 60 (1985), 107–121 (registered as
`prasad-raghunathan-1985-kneser-tits`), §2, printed p. 111 / PDF p. 6,
recalls the following. For a nonarchimedean local field `k` and a
connected, simply connected group, `H¹(k, ·)` is trivial. They attribute
the characteristic-zero case to Kneser and the general case to Bruhat–Tits.

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023)
(registered as `kaletha-prasad-2023-bruhat-tits-new-approach`),
Theorem 10.6.4, printed p. 399 / PDF p. 430, states that `H¹(k, G)` is
trivial for every simply connected semisimple `k`-group `G`. This is under
the standing assumptions of Chapter 10 (printed p. 389 / PDF p. 420): a
discretely valued field with Henselian valuation ring and perfect residue
field of dimension at most one. A nonarchimedean local field satisfies
these assumptions, since its residue field is finite.

The present proposition is the finite-Galois Čech consequence of that
vanishing, written with the Library's scheme-valued cocycles. A semisimple
group is smooth, so `H¹(F, G)` is the Galois cohomology of `G(F^sep)`. For a
finite Galois `M/F`, inflation `H¹(Gal(M/F), G(M)) → H¹(F, G)` is
injective, so the source vanishes as well. The Library theorem
`Langlands.GroupScheme.GaloisCocycle.isTrivial_iff` identifies triviality of
a scheme cocycle on the spectrum of a finite Galois extension with the
Galois coboundary identity for its crossed homomorphism. It is stated for
the Library's `GaloisCocycle.cover` presentation of that spectrum. This
paragraph explains where the formulation comes from. The module does not
prove the inflation argument or apply that comparison theorem, and it does
not define a Galois cohomology object.

## Purpose

The finite Galois form is the core arithmetic input for the separable-cover
statement. On a finite Galois cover, a cocycle can be rewritten as a crossed
homomorphism on the finite group `Gal(M/F)`, and Bruhat–Tits arguments with
Galois-stable chambers work in that setting. Only the reduction from
separable to Galois covers is proved, in the companion module. The vanishing
itself is not proved here or in that module.
