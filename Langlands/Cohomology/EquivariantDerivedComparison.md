# Derived equivariant sections and cohomology of the underlying sheaf

Author: Worker 13. Combines Worker 13's `Langlands.Cohomology.EquivariantDerivedSections`,
`Langlands.Cohomology.TopologicalDerivedSections`, `Langlands.Cohomology.DerivedComparison`
and `Langlands.Sheaf.Equivariant.Induction` with Worker 61's
`Langlands.Sheaf.Equivariant.Exact`.

Let `R` be a commutative ring and let a group `G` act on a topological space
`X` by continuous translations, all in one universe `u`. For an equivariant
module sheaf `F`, the derived functors `globalDerived R G X q` and
`compactDerived R G X q` produce representations of `G`. This module
identifies their underlying modules with the ordinary cohomology and the
compactly supported cohomology of the underlying sheaf `toSheaf F`, naturally
in `F`.

## Statements

`globalSectionsForgetIso` identifies the module underlying the global section
representation with the published ordinary global-section functor
`Langlands.Sheaf.CompactSupport.globalSections` of the underlying sheaf, by
identity components. The compact analogue is the published
`EquivariantDerivedSections.compactSectionsForgetIso`.

`globalDerivedForgetIso R G X q` is a natural isomorphism between two functors
on equivariant module sheaves. One is `globalDerived R G X q` followed by the
forgetful functor from `Rep R G` to `ModuleCat R`. The other is `toSheaf`
followed by `TopologicalDerivedSections.ordinaryCohomology (TopCat.of X) R q`.
`compactDerivedForgetIso R G X q` is the same for `compactDerived R G X q` and
`TopologicalDerivedSections.compactCohomology (TopCat.of X) R q`.

## Proof

Both isomorphisms are instances of
`DerivedComparison.rightDerivedCompIso`. Its hypotheses hold as follows:

- the forgetful functor from `Rep R G` to `ModuleCat R` is exact (Mathlib);
- `toSheaf G X (ModuleCat R)` is additive and exact (Worker 61's
  `toSheaf_additive` and `toSheaf_preservesHomology` in
  `Langlands.Sheaf.Equivariant.Exact`);
- `toSheaf` preserves injective objects (`toSheaf_preservesInjectiveObjects`
  in `Langlands.Sheaf.Equivariant.Induction`, from its exact left adjoint).

So an injective resolution of `F` maps to an injective resolution of
`toSheaf F`. Section functors of both resolutions agree termwise after
forgetting the action.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.5, Corollary 1.5.2(i), printed pp.11–12,
gives canonical isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^* F)`. Here
`H^q_c(X{G}, F)` is defined (printed p.11) by the derived functors of the
colimit, over open subgroups `N`, of `N`-invariant compactly supported
sections. Worker 13 read this passage in the original. For a discrete group
the trivial subgroup is open, so this colimit is just the compactly supported
sections of the underlying sheaf. The underlying module of `compactDerived`
then has the shape of Berkovich's `H^q_c(X{G}, F)`, and
`compactDerivedForgetIso` is the analogue of Corollary 1.5.2(i) for the
discrete group `G` on the ordinary-topological transport site. Berkovich
proves the corollary through softness of the Godement resolution (Proposition
1.5.1). This module uses an exact left adjoint of the forgetful functor
instead.

The group carries no topology here. Discreteness or smoothness of the action
on cohomology, the Hochschild–Serre spectral sequence
`H^p(G, H^q_c(X, b^*F)) ⇒ H^{p+q}_c(X(G), F)`, invariant derived sections,
the Godement-route comparison and the analytic étale site are not treated.

Source registration:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

All imported modules are present in Library commit
`9a0767626050f3346ad5f25e37cef39f38a5c0dc`.
