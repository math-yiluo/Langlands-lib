# Coinduction of sheaves to equivariant sheaves

Author: Worker 61. Built on the published transport category
`Langlands.Sheaf.Equivariant.ActionOpens`, the transport site and sheaf
equivalence `Langlands.Sheaf.Equivariant.Site`, and the forgetful functor
`toSheaf` of `Langlands.Sheaf.Equivariant.Topological`. It imports Worker
13's `Langlands.Sheaf.Equivariant.Induction`, the left adjoint of `toSheaf`,
and is the dual construction.

Let a group `G` act on a topological space `X` by continuous translations,
with `G` and `X` in one universe `u`. Let `A` be a coefficient category
with all limits indexed by categories in universe `u`
(`HasLimitsOfSize.{u, u} A`). `toSheaf G X A` forgets the group-labelled
arrows of an equivariant sheaf. This module constructs a right adjoint of
`toSheaf G X A`, called coinduction.

## The inclusion lifts covers

A sieve on an ordinary open in the transport site covers exactly when its
label-one inclusions form an ordinary open cover. This is how the published
`transportTopology` is defined. The ordinary covering condition for the sieve
pulled back along `ActionOpens.inclusion G X` is therefore literally the
transport covering condition. The instance `inclusion_isCocontinuous` records
that the inclusion of ordinary opens is cocontinuous (cover-lifting, SGA 4 III
2.1) from the ordinary open-cover topology `Opens.grothendieckTopology X` to
`transportTopology G X`. Its proof is the identity on the covering
hypothesis.

## Coinduction

Mathlib's `ran_isSheaf_of_isCocontinuous` (SGA 4 III 2.2) shows that right
Kan extension along a cocontinuous functor sends sheaves to sheaves.
`transportCoinduction` is Mathlib's resulting functor
`Functor.sheafPushforwardCocontinuous` for the inclusion. It sends an ordinary
sheaf to the right Kan extension of its underlying presheaf along the opposite
of the inclusion, a transport sheaf. `coinduction` composes it with the
inverse of the published equivalence `sheafEquivalence` between transport
sheaves and equivariant sheaves:

`coinduction G X A : TopCat.Sheaf A (TopCat.of X) ⥤ TopologicalSheaf G X A`.

Mathematically, the sections of `coinduction F` over an open `U` are the
product of the sections of `F` over the translates `g⁻¹ • U` for `g` in `G`.
The module does not construct this description. Both the definition and the
adjunction below use only the right Kan extension.

## Adjunction and injectives

`toSheafIsoPushforward` identifies restriction of transport sheaves along the
inclusion, after the equivalence, with `toSheaf`. Its components are
identities. Naturality holds in every coefficient category; the proof uses
the identity and composition laws rather than definitional unfolding.

The inclusion is continuous (the published `inclusion_isContinuous`) and
cocontinuous. So Mathlib's `Functor.sheafAdjunctionCocontinuous` shows that
restriction along the inclusion is left adjoint to `transportCoinduction`.
`coinductionAdjunction` composes this adjunction with the equivalence and the
isomorphism above. It proves `toSheaf G X A ⊣ coinduction G X A`. The
instances record that `toSheaf G X A` is a left adjoint and that
`coinduction G X A` is a right adjoint.

For module coefficients over a commutative ring `R` in universe `u`, the
instance `coinduction_preservesInjectiveObjects` shows that coinduction
sends injective ordinary sheaves to injective equivariant sheaves. It applies
Mathlib's
`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`.
That theorem needs the left adjoint `toSheaf` to preserve monomorphisms.
The published `Limits` module proves that `toSheaf` preserves all limits
that exist in the coefficient category, in particular pullbacks. Instance
inference derives preservation of monomorphisms from this.

## Provenance and scope

The module is derived infrastructure. It is the standard right adjoint of
the functor that forgets equivariance. It is needed for the Godement
construction of sheaves on an equivariant site that Harris uses.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), section 2, printed p.304, uses Berkovich's smooth equivariant
version of the Godement flasque resolution. It is an embedding `T → F(T)`,
and Harris states that `F(T)` is the composition of two functors, denoted
`C^0 = ν_* ν^*` and `b^*` by Berkovich. Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*
(unfinished 1995–1996 manuscript), section 1.5, printed p.10, defines
`C^0(F) = ν_* ν^*(F)` for a morphism of sites `ν` from a discrete set of
points to the equivariant étale site `X(G)`. Observation (a) in the proof of
Proposition 1.5.1, printed p.10, describes `ν_* ν^* F` restricted to an open
subgroup `N` through the coset decomposition `G = ∐ g_j N` and the
translated points `g_j⁻¹ x_i`. So pushing forward from points to the
equivariant site introduces a product over group translates. Coinduction is
this group factor on the ordinary-topological transport site. Worker 61 read
these passages in the original.

The setting is the ordinary-topological transport site of an abstract group
action, not Berkovich's analytic étale site. The module makes no smoothness
claim. For a topological group, a smooth Godement construction must follow
coinduction with a smooth-part functor, which this module does not provide.
The module claims no flasqueness, exactness or cohomology comparison.

Source registrations:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Harris 1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the published `Induction`, `Site`, `ActionOpens` and
`Topological` modules and Mathlib's `CategoryTheory.Sites.CoverLifting`,
pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
