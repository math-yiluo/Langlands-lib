# Coordinatewise products of original nonunital modules

Authors: Workers 6, 702 and 185.

## Construction and scope

`Langlands.Algebra.NonUnitalModule.pi` puts the coordinatewise original action
on a dependent function group. It accepts any `A : Type uA` with
`NonUnitalRing A`, any `I : Type uI`, and any family `M : I → Type uM` with
its specified additive groups and `NonUnitalModule A (M i)` actions. The
carrier is the actual function type `∀ i, M i`, in `Type (max uI uM)`.
Its additive group is the usual pointwise group, and its action is
`(a • m) i = a • m i`. The three universes are independent.

The bundled constructions use `I : Type` and
`M : I → NonUnitalModuleCat.{uA,uM} A`. This index restriction ensures that
the function carrier is still in `Type uM`; it does not enlarge the carrier
universe or identify it with the ring universe.

| Lean name in `Langlands.Algebra.NonUnitalModuleCat` | Meaning |
| --- | --- |
| `concreteProduct M` | The original module on the actual carrier `∀ i, M i`. |
| `concreteProductπ M i` | The original additive intertwiner `m ↦ m i`. |
| `concreteProductLift M f` | For `f i : N ⟶ M i`, the original intertwiner `n ↦ (fun i => f i n)`. |
| `concreteProductFan M` | The actual Mathlib `Fan M` with that vertex and those projections. |
| `concreteProductIsLimit M` | An actual `IsLimit (concreteProductFan M)`, including its universal lift and uniqueness. |
| `concreteHasProduct M` | `HasProduct M`, furnished by that cone and its universal property without an assumed product. |
| `productIsoConcrete M` | Under `[Finite I]`, an isomorphism from the existing selected product `∏ᶜ M` to the concrete product. |

Every map is a morphism of the published original-action category. Neither the
objects nor their morphisms are replaced by unital modules. The ring need not
be commutative, unital, nontrivial or idempotented. Its existing unit, if any,
need not act as the identity. Zero actions, zero groups and the empty index
are admitted. No nondegeneracy, finite generation or finite dimension is
assumed. Finiteness is used only for the comparison with the category's
already selected product.

The module supplies no new global product instance. In particular, arbitrary
base-universe families have the explicitly exhibited product and
`concreteHasProduct`, while the selected-product comparison reuses the
published `NonUnitalModuleCat.hasFiniteProducts`. Families in a larger index
universe are supported by the unbundled action construction only; this file
does not state a same-carrier-universe product theorem for them.

## Intrinsic laws and implemented proof

The coordinatewise module instance verifies the five original action laws by
function extensionality and the corresponding given action law in each
coordinate. The projections and universal lift satisfy additivity, preservation
of zero and intertwining directly. The laws `concreteProduct_zero_apply`,
`concreteProduct_add_apply`, `concreteProduct_neg_apply` and
`concreteProduct_smul_apply` identify the actual operations. The evaluation
laws `concreteProductπ_apply` and `concreteProductLift_apply` identify the
actual original maps.

`concreteProductLift_π` states
`concreteProductLift M f ≫ concreteProductπ M i = f i`.
`concreteProduct_hom_ext` proves equality of two original maps into the product
from equality after every coordinate projection. Its proof uses the published
extensionality of `NonUnitalModuleHom`, function extensionality, and evaluation
of the given morphism equalities. It gives `concreteProductLift_eta`, which
recovers any map from its coordinates. `concreteProductLift_comp` proves that
assembling maps commutes with precomposition by an original morphism.

`concreteProductIsLimit` applies Mathlib's `Fan.IsLimit.mk` to the actual
coordinate lift. The projection law establishes the factorization condition,
and `concreteProduct_hom_ext` establishes uniqueness. This proves the product
universal property inside the original category directly; it is not inferred
from an assumed universal property. `concreteHasProduct` packages this cone.

For a finite family, the selected limit's universal property and the constructed
one give `productIsoConcrete` by `conePointUniqueUpToIso`. Both projection
identities are retained:

```lean
(productIsoConcrete M).hom ≫ concreteProductπ M i = Pi.π M i
(productIsoConcrete M).inv ≫ Pi.π M i = concreteProductπ M i
```

These are `productIsoConcrete_hom_π` and `productIsoConcrete_inv_π`.
`productIsoConcrete_lift` then identifies
`Pi.lift f ≫ (productIsoConcrete M).hom` with `concreteProductLift M f`
by coordinate extensionality and these projection identities.

The Lean file checks the complete unapplied type of every named construction
and law at independent `uA,uM` (and independent `uI` for the unbundled action).
It additionally checks the full `concreteProductIsLimit`, `productIsoConcrete`,
both comparison projection laws and the comparison lift law at
`(uA,uM)=(0,1)` and `(1,0)`. The unbundled instance's explicit universe-argument
order is `pi.{uA,uM,uI}`.

## Source correspondence

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant original passages were read:

- Printed pp.5–6/PDF11–12 specify the ambient additive module conventions,
  including the absence of an original unit-action law.
- A.IV.1 example 3, printed p.257/PDF263, defines a family product as a limit
  over the corresponding discrete category.
- The abelian-group example in A.IV.2, printed pp.257–258/PDF263–264,
  identifies the product with the Cartesian product carrying the pointwise
  group operations and canonical projections.
- I.1.2, printed p.7/PDF13, defines the nondegenerate full subcategory and
  asserts its submodule/quotient closure and abelianness. A.VI.1, printed
  p.261/PDF267, includes finite products among the abelian-category axioms.

This file is internally derived infrastructure: it extends the displayed
abelian-group product to the published original ring actions, verifies its
categorical universal property, and compares it with the already selected
finite product. The original does not give these Lean declarations or a
separately numbered theorem in this exact form.

The registered supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF1–3 and PDF18–19, was checked for the relevant conventions and Appendix A
corrections. It concerns the earlier edition and does not replace the 2026
reference or supply this construction. The public note
`notes/renard/appendix-a-corrections.md` records the missing finite-product
hypothesis in the source's unrestricted full-subcategory criterion and the
arrow/constant-functor issues in its general limit prose. The present cone
uses actual morphisms into an explicit vertex and requires no connectedness
or nonemptiness of the index.

This unit does not prove closure of nondegenerate modules under finite
products, their abelianness, the exactness of their inclusion or of the
nondegenerate-part functor, nor a claim about infinite products in that
subcategory. Those require separate published statements and proofs.
