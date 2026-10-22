# Rigidified sheaves of modules

For schemes `S` and `X` and an actual morphism `ε : S ⟶ X`, a
`Langlands.SchemeModule.RigidifiedModule ε` consists of an actual sheaf of
modules `M : X.Modules` and an isomorphism
`structureModule S ≅ (Scheme.Modules.pullback ε).obj M`. The pullback is
Mathlib's constructed pullback of sheaves of modules. Both schemes have
universe `u`; no property of `ε` is imposed here.

A morphism from `(M, α)` to `(N, β)` is a module morphism `f : M ⟶ N`
satisfying `α.hom ≫ ε⁎(f) = β.hom`. The category instance constructs identities
and composites from the underlying module category. The compatibility of a
composite follows from functoriality of pullback, and the category laws follow
from those of module morphisms. `RigidifiedModule.forget` is a faithful functor
to `X.Modules`.

`RigidifiedModule.isoMk` constructs an isomorphism of rigidified modules from
an underlying module isomorphism satisfying the displayed compatibility. The
inverse compatibility follows by composing with its inverse after pullback.
`transport M e` moves the rigidification across a module isomorphism `e` by
composing it with the pullback of `e`. `transportIso M e` is the resulting
isomorphism of rigidified modules. These are constructions, including the
required inverse and category laws.

## Provenance and scope

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
draft, Chapter VI §1, paragraph (6.2), printed p.88 (PDF p.92), registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, PDF SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The source defines a rigidification of a line bundle on `X ×_S T` along the
base-changed section as `O_T ≅ ε_T⁎ L`, and defines compatible homomorphisms
by the same commuting equation used here.

This module is derived infrastructure that isolates the rigidification data
and its category before imposing the line-bundle condition. It deliberately
allows arbitrary modules and arbitrary morphisms `ε`. The category, inverse
and transport constructions do not require the source's extra hypotheses on
`X → S`, which are used there to obtain additional conclusions such as absence
of nontrivial automorphisms and comparison with the fppf Picard functor. No such
conclusion is asserted here. In particular, this module does not construct
invertible modules, the tensor-product group law, base-change of rigidified
bundles, their Picard functor, a Poincaré bundle or representability. Subsequent
line-bundle and relative constructions must supply those additional parts.
