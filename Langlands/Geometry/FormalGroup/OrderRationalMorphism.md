# Order-equivariant rational maps and quasi-isogenies

This module constructs rational formal homomorphisms that commute with actual
order actions, and their invertible maps. It uses the finite-coordinate formal
modules and coefficient extension of the preceding modules.

The declarations are in
`Langlands.FormalGroup.ModuleLaw.OrderAction`.

## Source and provenance

Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2 A, printed p.109,
defines a quasi-isogeny of formal `O`-modules as an invertible element of
`Hom(X,Y) ⊗_O F`. The subsequent definition equips a formal `O`-module with an
action of `O_D` extending its `O`-action. This module combines these two
definitions for an arbitrary, possibly noncommutative, `O`-algebra `A`.

The original source is registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The submodule and transport API are derived constructions: their equations
refer to the actual formal homomorphisms defining the order actions and to
composition on the tensor Hom.

## Equivariant rational Hom

Let `O` be a commutative ring, `R` a commutative `O`-algebra, `A` an
`O`-algebra, and `F` a field with an `O`-algebra structure. Let `M,N` be
finite-coordinate formal `O`-modules over `R`, and let `E,E'` be their
respective `A`-actions.

`rationalHomSubmodule F E E'` is the `F`-submodule of
`ModuleLaw.RationalHom F M N` whose members satisfy, for every `a : A`,

```text
f ∘ ofHom(E.action a) = ofHom(E'.action a) ∘ f.
```

The ambient space is the actual tensor product `F ⊗_O Hom(M,N)`; the
preceding module supplies its canonical equivalence with
`Hom(M,N) ⊗_O F`. `RationalHom F E E'` is the subtype of this submodule.
The forgetful `toLinearMap` is its injective linear inclusion.

`RationalHom.ofHom` rationalizes an integral order-linear formal map.
Identity and composition are the ambient rational identity and composition,
with their commutation equations proved from the integral equations and
associativity. The module proves the identity, associativity, additive and
`F`-scalar composition laws, packages composition as `compLinear`, and
equips `RationalHom F E E` with its composition ring structure.
Rationalization preserves identity and composition.

For an `O`-algebra homomorphism `θ : R → S`, `RationalHom.map θ` restricts
the actual coefficient-extension map on tensor Hom. Applying that map to
the commutation equation and using its composition and rationalization laws
establishes equivariance for the coefficient-extended order actions.
The accompanying laws show preservation of identity, composition and
integral rationalization.

## Equivariant quasi-isogenies

Assume in addition that `O` is a domain and `F` is its fraction field.
`QuasiIsogeny F E E'` consists of an equivariant rational map and an
equivariant rational inverse, with both inverse equations.
`toModuleQuasiIsogeny` forgets equivariance and retains these actual maps.

`inverse_commutes` proves that equivariance of the forward map already
forces equivariance of its inverse. The proof inserts
`id_N = f.hom ∘ f.inv`, reassociates, uses the forward commutation equation,
and cancels `f.inv ∘ f.hom = id_M`. Consequently,
`ofModuleQuasiIsogeny` upgrades an underlying quasi-isogeny from its forward
equivariance alone. Forgetting this upgrade returns the original
quasi-isogeny.

The module constructs identity, inverse, composition, and rationalization
of an actual order-linear isomorphism. The inverse is uniquely determined
by the forward map, so equality of forward equivariant rational maps
detects equality of quasi-isogenies. Coefficient extension applies to both
inverse maps; its laws preserve identity, inverse, composition and
rationalization of isomorphisms.

## Scope

The construction is for global finite coordinates and an arbitrary actual
`A`-action. It does not identify this submodule with
`F ⊗_O Hom_A(M,N)` for arbitrary orders. It supplies no maximal-order
specialization, height, intrinsic gluing, nilpotent rigidity, framing
object, moduli functor or representability theorem.
