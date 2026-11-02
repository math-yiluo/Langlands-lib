# Actual abelian-sheaf cohomology as right-derived global sections

Worker 368. This internal adapter identifies Mathlib's actual Ext-defined
cohomology of abelian sheaves with right-derived evaluation on the whole
space. The space `X : TopCat.{u}`, its sheaves of abelian groups with
section groups in universe `u`, and the degree `n : ℕ` are arbitrary.
There is no separation, finiteness or geometric hypothesis on `X`.

All declarations are in
`Langlands.Cohomology.AbelianSheafDerivedSections`.

`constantIntegers X` is the actual constant sheaf with values `ULift.{u} ℤ`.
It is constructed by Mathlib's `constantSheaf`, which sheafifies the
constant presheaf. It is exactly the first argument of the Ext group in
Mathlib's `Sheaf.H.{u} F n`. The universe lift ensures that the constant
group belongs to `AddCommGrpCat.{u}`.

`globalSections X` evaluates the underlying presheaf at the top open.
It is additive and is right adjoint to the constant-sheaf functor, hence
preserves finite limits. These facts are supplied as instances.

`homGlobalSectionsIso X` is a natural isomorphism

```text
Hom(constantIntegers X, -) ≅ globalSections X
```

of functors to abelian groups, with Hom realized by Mathlib's
`preadditiveCoyoneda`. Its component at `F` is the composite additive
equivalence

```text
Hom(ℤ_X, F) ≃+ Hom(ULift ℤ, F(X)) ≃+ F(X).
```

The first equivalence is `constantSheafAdj.homAddEquiv` at the terminal
open. The second is `AddCommGrpCat.uliftZMultiplesAddEquiv`, evaluation
of an additive homomorphism on the lifted generator. Naturality follows
from naturality of the adjunction and evaluation on that generator.

`homRightDerivedIso X n` derives the Hom/global-sections isomorphism.
The two maps are `NatTrans.rightDerived` applied to its two maps.
The identities follow from preservation of identity and composition by
`NatTrans.rightDerived`. Thus this derived comparison is also natural
in the coefficient sheaf.

`HAddEquiv X F n` is the additive equivalence

```text
Sheaf.H.{u} F n ≃+ ((globalSections X).rightDerived n).obj F.
```

It first applies the published
`ExtRightDerived.extAddEquivRightDerived (constantIntegers X) F n`,
then the component of `homRightDerivedIso X n`. The Grothendieck abelian
sheaf category supplies the required injective resolutions and
`HasExt.{u}` instance. This construction covers degree zero and all
positive degrees.

The provenance is an internal composition of the published generic
Ext/right-derived-Hom comparison with pinned Mathlib's actual constant
sheaf, adjunction and right-derived functors. No external theorem or
unpublished flasque-sheaf result is used.

This file does not assert naturality of `HAddEquiv`, compatibility with
connecting maps, or a module structure on its source. The imported
Ext/right-derived-Hom comparison provides an additive equivalence without
these additional compatibility statements. The file also does not
compare module cohomology with abelian-sheaf cohomology, classify
line bundles or prove Picard representability; those remain separate
obligations.
