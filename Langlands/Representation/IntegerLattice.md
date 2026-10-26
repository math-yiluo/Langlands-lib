# Commuting invertible tuples and integer-lattice representations

This module constructs the equivalence in the opening paragraph of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July
2026, Appendix C.III, printed page 279 / PDF285. The governing source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF285 and the continuation PDF286 were read directly. The source starts with a
finite-dimensional complex vector space and pairwise commuting invertible maps,
and identifies their integer-power compositions with an action of the integer
lattice.

The construction here works in arbitrary dimension and for `V : Type u` with
arbitrary `u`. This is an explicit strengthening: the algebraic equivalence does
not use finite dimensionality. `finiteDimensionalTupleRepresentationEquiv` gives
the source's finite-dimensional specialization with no additional assumptions.
The subsequent exponential-polynomial coefficient proposition, its eigenspace
arguments and its binomial expansion are outside this unit.

For the errata check, the [author's book page](https://perso.pages.math.cnrs.fr/users/david.renard/)
was read on 26 October 2026 and retained as `renard-author-page-2026-10-26`,
SHA256 `143092e92be11be1b9c5a03bfc1e9e4538edb45f9a67d5fc8cc474b7b6dcd580`.
It links the corrected French 2026 edition and separately labels the 2010
edition's errata; its book section supplies no separate 2026 errata link. The
current linked errata file matches registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
Its appendix portion, PDF18–19, was read. It contains no correction to the
opening tuple/representation equivalence. Its final correction concerns
parentheses in the later matrix-block formula; the 2026 source governs here.
No project Renard errata note was found at preparation time.

All public names below are in `Langlands.IntegerLattice`.

## Objects and conventions

`Lattice d` abbreviates `Multiplicative (Fin d → ℤ)`. This is the actual additive
integer lattice with its law written multiplicatively, as required by Mathlib's
`Representation`. Thus multiplication of wrapped lattice points is coordinate
addition, the group identity is the zero vector and inversion negates every
coordinate. No lattice basis for the vector space `V` is introduced.

`generator d i` is exactly `Multiplicative.ofAdd (Pi.single i 1)`, the standard
lattice basis vector in coordinate `i`. The coordinates are indexed by `Fin d`,
so Lean numbers them from zero; these correspond to the source's indices
`1, ..., d` after shifting by one.

`CommutingInvertibleTuple d V` is the subtype

```lean
{ u : Fin d → (Module.End ℂ V)ˣ // Pairwise fun i j => Commute (u i) (u j) }
```

These are units of the actual algebra of complex-linear endomorphisms. Each
entry stores an endomorphism, its two-sided inverse and both inverse equations.
`Pairwise` checks distinct indices; a map commutes with itself automatically.
There is no assumption that a representation realizing the tuple already exists.

Multiplication of linear endomorphisms means composition: `a * b` acts on `v`
as `a (b v)`. Consequently the source expression `u₀^n₀ ∘ ... ∘ u_(d-1)^n_(d-1)`
has its rightmost factor acting first. The construction uses
`Finset.univ.noncommProd` of the units `u i ^ n.toAdd i`; Mathlib defines this
finite product using the given pairwise commutation proof. Every integer power
of distinct commuting entries commutes, by `Commute.zpow_zpow`, so the product
is independent of its enumeration and may be read in increasing coordinate
order. Every exponent has type `ℤ`. In particular, negative coordinates use the
stored inverses in the unit group, with no truncation or natural-number coercion.

## Actual maps and intrinsic laws

`tupleRepresentationEquiv d V` has type

```lean
CommutingInvertibleTuple d V ≃ Representation ℂ (Lattice d) V
```

Its forward function is the actual representation. For every wrapped lattice
point `n`, `tupleRepresentationEquiv_apply` identifies its linear map with the
underlying endomorphism of

```lean
Finset.univ.noncommProd (fun i => u.1 i ^ n.toAdd i) ...
```

The ellipsis here denotes the commutation proof, explicitly present in Lean.
`tupleRepresentationEquiv_apply_apply` is the same formula on an arbitrary
vector. Both apply to every integer lattice point, including points with mixed
positive and negative coordinates.

The reverse function is generator evaluation.
`tupleRepresentationEquiv_symm_apply` states the exact unit-valued formula

```lean
((tupleRepresentationEquiv d V).symm ρ).1 i =
  ρ.asGroupHom (generator d i)
```

`tupleRepresentationEquiv_symm_apply_coe` identifies its underlying linear map
with `ρ (generator d i)`. `tupleRepresentationEquiv_symm_apply_inv` identifies
its inverse endomorphism with `ρ ((generator d i)⁻¹)`, the action at the negative
standard generator. Thus invertibility comes from the representation's group
law. `generator_values_commute` proves commutation for any two generator values
by mapping commutation in the abelian lattice through `ρ.asGroupHom`.

`tupleRepresentationEquiv_asGroupHom_generator` recovers each original tuple
entry as an exact unit, and `tupleRepresentationEquiv_generator` recovers its
underlying endomorphism. `tupleRepresentationEquiv_left_inv` reconstructs the
entire commuting tuple from these generator values, including its subtype
proof. `tupleRepresentationEquiv_right_inv` reconstructs the entire
representation. `representation_eq_product` also expresses every value of an
arbitrary representation as the finite product of the integer powers of its
own invertible generator values.

## Implemented construction and proof

The equivalence is the composition of four concrete equivalences. The internal
helpers are implementation details derived from Mathlib's universal
constructions, rather than separate assertions from Renard.

1. `powersFamilyEquiv` sends each tuple entry to `zpowersHom`, the homomorphism
   from `Multiplicative ℤ` given by all its integer powers. Commuting images
   follow from `Commute.zpow_zpow`. The inverse evaluates at `ofAdd 1`.
   The left inverse is `zpow_one`; the right inverse is the inverse law of
   `zpowersHom` for every coordinate homomorphism.
2. `MonoidHom.noncommPiCoprodEquiv` identifies these families of homomorphisms
   with commuting images with homomorphisms from the finite product
   `Fin d → Multiplicative ℤ`. Its forward function is the finite noncommutative
   product, and its inverse restricts to each single-coordinate subgroup. Its
   homomorphism and both inverse laws are supplied by that Mathlib construction.
3. `coordinateEquiv`, an instance of `MulEquiv.piMultiplicative`, moves the
   multiplicative wrapper through the function type. Precomposition turns the
   finite-product homomorphism into a homomorphism from `Lattice d`. The private
   lemma `coordinateEquiv_generator` verifies pointwise that a standard lattice
   generator corresponds to a single-coordinate group generator.
4. `unitsRepresentationEquiv` forgets units to endomorphisms by composing with
   `Units.coeHom`, yielding an actual `Representation`. Its inverse is
   `Representation.asGroupHom`, which uses `ρ (g⁻¹)` as the inverse of `ρ g`.
   Both inverse laws are proved by extensionality and reflexivity of the
   underlying values; equality of units uses equality of their values.

Composition gives both inverse laws without an assumed realization or an
existence certificate. The public product formula is definitional equality.
The reverse generator formula reduces the composite inverse and uses
`coordinateEquiv_generator`. Exact recovery of each unit follows by evaluating
the composed left-inverse law at that coordinate; coercion gives the
endomorphism formula. The inverse-entry formula uses preservation of inversion
by the units-valued homomorphism. The representation product-reconstruction
formula specializes the forward product formula to the reverse tuple, then
uses the right-inverse law and the reverse generator formula.

## Degenerate cases and provenance

All constructors work with `d = 0`; `tupleRepresentationEquiv_zero` explicitly
proves that the resulting action is the identity, the empty product. The
construction requires only `AddCommGroup V` and `Module ℂ V`: it also applies to
the zero vector space and imposes no `Nontrivial V` hypothesis. It uses no
topology, eigenvalues, simultaneous diagonalizability, or choice of a basis of
`V`.

Worker 6 supplied the source scope and identified the Mathlib universal-product,
integer-power and units APIs. Worker 466 assembled the equivalence, proved the
intrinsic formulas and inverse laws, and wrote this documentation. The internal
helpers and corollaries are derived algebraic implementation content explaining
the source's opening equivalence, rather than additional source claims.
