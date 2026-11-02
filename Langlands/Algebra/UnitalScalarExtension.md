# Unital scalar extension over possibly noncommutative rings

Module `Langlands.Algebra.UnitalScalarExtension`. Entry declaration:
`Langlands.Algebra.UnitalScalarExtension.functor`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.V.2, the example on
printed pp.260–261 (one-based PDF266–267). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The example reads: let A be a unital ℂ-algebra and B a subalgebra
("sous-algèbre") of A. Every unital left A-module is also a B-module, giving a
forgetful functor `F : M(A) → M(B)`. Its left adjoint, the base-change functor,
is `P_B^A : N ↦ A ⊗_B N`. The example then defines θ, σ, η and ε.

The source does not spell out whether B contains 1. The forgetful functor
lands in `M(B)`, the category of unital B-modules, and θ uses `1 ⊗ x`. So
we read B as a unital subalgebra. Mathlib's `Subalgebra k A` contains 1 by
definition. A is not assumed commutative.

The supplementary older-edition corrections, source
`renard-2010-corrections-complements`, PDF18–19, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, list two
corrections for this example (2010 edition, p.301: "B-morphisme" should read
"A-morphisme", and a parenthesization fix). The 2026 text already contains
both corrections, and it governs here. Neither correction affects the
definitions in this unit.

The source example is the special case k = ℂ of the subalgebra section below.
Most of this unit is internal infrastructure derived from that example: the
generalization to an arbitrary unital ring homomorphism `φ : B →+* A`, the
general commutative coefficient ring k, and the named adapters
(`rightModule`, `nonUnitalHom`, `residualModule`, `residualMap`).
The generalization assumes neither commutativity of A or B nor injectivity
of φ.

## Construction

Throughout, `B : Type uB` and `A : Type uA` are rings (`Ring`, so unital,
possibly noncommutative), and `φ : B →+* A` is a unital ring homomorphism.

### The right B-action on A

- `rightModule φ : NonUnitalModule Bᵐᵒᵖ A` is the published right regular
  action `NonUnitalModule.rightRegular A`, pulled back along
  `φ.op.toNonUnitalRingHom` by `NonUnitalModuleRestrictScalars.module`.
- `rightModule_action` and `rightModule_smul` compute this action as
  `op b • a = a * φ b`. The first states it through
  `NonUnitalModule.toEndHom`. The second states it with the scalar
  multiplication of this explicitly named instance. Both hold by `rfl`.
- `actionsCommute φ` proves that the original left multiplication
  `NonUnitalModule.regular A` commutes with this right action:
  `(a * x) * φ b = a * (x * φ b)` by associativity.

### The tensor quotient and its unital A-module structure

For an ordinary B-module `M : Type uM` (`AddCommGroup M`, `Module B M`):

- `Tensor φ M : Type (max uA uM)` is by definition the published
  `NonUnitalModuleTensor.Tensor B A M`, using `rightModule φ` on A and
  `NonUnitalModule.ofModule B M` on M. This is the quotient of the integer
  tensor product `A ⊗[ℤ] M` by the ℤ-span of all
  `(a * φ b) ⊗ m - a ⊗ (b • m)`. No tensor object or balancing law is
  taken as input.
- `tensorAddCommGroup` is the published quotient group
  `NonUnitalModuleTensor.addCommGroup B A M`. `tensorAddCommGroup_eq`
  records this by `rfl`.
- `tmul φ M a m` is the published pure tensor
  `NonUnitalModuleTensor.tmul B A M a m`, the class of `a ⊗ m` in the
  quotient. `tmul_eq` records this by `rfl`.
- `residualModule φ M : NonUnitalModule A (Tensor φ M)` is the published
  residual left action `NonUnitalBimoduleTensor.leftModule (actionsCommute φ) M`
  on the same quotient. `residualModule_eq` records this by `rfl`.
  `residualModule_action` gives its value on pure tensors:
  `a` sends `tmul φ M x m` to `tmul φ M (a * x) m`.
- `residualModule_one` proves that `1` acts as the identity additive map.
  The proof uses pure-tensor extensionality (`NonUnitalModuleTensor.hom_ext`)
  and `1 * a = a`.
- `module φ M : Module A (Tensor φ M)` turns the same residual action into an
  ordinary unital module via `NonUnitalModule.toModule` and
  `residualModule_one`. `module_smul` records that its scalar multiplication
  is literally the residual action (`rfl`).
- `tensorObj φ M : ModuleCat.{max uA uM} A` is `ModuleCat.of` on that quotient
  group and that module. `tensorObj_carrier`, `tensorObj_addCommGroup` and
  `tensorObj_module` identify the carrier, group and module by `rfl`.
- `smul_tmul` is the pure-tensor left-action equation for the ordinary
  module: `a • tmul φ M x m = tmul φ M (a * x) m`.
- `tmul_balanced` is the balancing equation
  `tmul φ M (a * φ b) m = tmul φ M a (b • m)`, from the published
  `NonUnitalModuleTensor.tmul_balanced`.
- `hom_ext` is pure-tensor extensionality for A-linear maps out of
  `tensorObj φ M` into any `Module A Z` with `Z : Type uZ`. Two such maps are
  equal if they agree on all `tmul φ M a m`. The proof applies the published
  `NonUnitalModuleTensor.hom_ext` to the underlying additive maps.

### Maps

For ordinary B-modules `M : Type uM`, `N : Type uN`, `P : Type uP`, with
independent universes:

- `nonUnitalHom f` repackages an ordinary B-linear map `f : M →ₗ[B] N` as an
  intertwiner `NonUnitalModuleHom B M N` for the adapted actions
  `NonUnitalModule.ofModule`. `nonUnitalHom_toAddMonoidHom` records that its
  additive map is `f.toAddMonoidHom`.
- `residualMap φ f` is the published
  `NonUnitalBimoduleTensor.leftMap (actionsCommute φ) (actionsCommute φ)
  (NonUnitalBimoduleHom.id A B A) (nonUnitalHom f)`. This is an intertwiner of
  the residual A-actions. `residualMap_toAddMonoidHom` records that its
  additive map is exactly the published original-action tensor map
  `NonUnitalModuleTensor.map B (NonUnitalBimoduleHom.id A B A).toRightHom
  (nonUnitalHom f)`. `residualMap_smul` is its residual intertwining law
  `residualMap φ f (a • t) = a • residualMap φ f t`.
- `tensorMap φ f : tensorObj φ M →ₗ[A] tensorObj φ N` is built from the
  additive map of `residualMap φ f` together with `residualMap_smul` as its
  linearity proof. `tensorMap_toAddMonoidHom` records this (`rfl`).
- `tensorMap_tmul`: `tensorMap φ f (tmul φ M a m) = tmul φ N a (f m)`.
- `tensorMap_id` and `tensorMap_comp` state the whole-map identity and
  composition laws:
  `tensorMap φ LinearMap.id = LinearMap.id` and
  `tensorMap φ (g.comp f) = (tensorMap φ g).comp (tensorMap φ f)`.
  Both follow from `hom_ext`, since each side agrees on pure tensors by `rfl`.

### The extension functor

- `functor φ : ModuleCat.{max uA uM} B ⥤ ModuleCat.{max uA uM} A` sends an
  object M to `tensorObj φ M` and a morphism f to
  `ModuleCat.ofHom (tensorMap φ f.hom)`. Its functor laws come from
  `tensorMap_id` and `tensorMap_comp`. This is the Lean counterpart of the
  source's `P_B^A`.
- `functor_obj`, `functor_obj_carrier`, `functor_map_hom` and
  `functor_map_tmul` compute the object (`tensorObj φ M`), its carrier
  (`Tensor φ M`), the morphism (`tensorMap φ f.hom`) and its value on pure
  tensors (`tmul φ N a (f.hom m)`), all by `rfl`.

### Universes

The ring universes uB and uA and the carrier universes uM, uN, uP, uZ are
independent variables. `Tensor φ M` lies in `Type (max uA uM)`, because the
quotient is formed inside `A ⊗[ℤ] M`. B appears only through the relations
that span the submodule, so uB does not occur in the carrier universe.
Hence `tensorMap` keeps independent input and output carrier universes uM and
uN.

The bundled functor uses the same carrier universe `max uA uM` for both
module categories. That universe is closed under tensoring with A: if
`M : Type (max uA uM)`, then `Tensor φ M : Type (max uA (max uA uM))`, which
is `Type (max uA uM)`. This imposes no relation between uB and uA or uM. The
inspected entry declaration `functor` has exactly the level parameters
uB, uA, uM.

### Restriction

- `restriction φ : ModuleCat.{uM} A ⥤ ModuleCat.{uM} B` is Mathlib's native
  `ModuleCat.restrictScalars φ`, at any carrier universe uM independent of uA
  and uB. It is the Lean counterpart of the source's forgetful functor F.
- `restriction_obj_carrier`: the carrier of the restricted object is the
  carrier of M.
- `restriction_obj_isModule`: its module structure is `Module.compHom M φ`.
- `restriction_smul`: `b • m = φ b • m`.
- `restriction_map_function` and `restriction_map`: the underlying function
  of a restricted morphism is the original function `f.hom`.

All five hold by `rfl`.

### Subalgebra specialization

Let `k : Type uk` be a commutative ring, `A` a possibly noncommutative
k-algebra (`Ring A`, `Algebra k A`), and `S : Subalgebra k A`.

- `subalgebraFunctor S` is `functor S.val.toRingHom`, and
  `subalgebraRestriction S` is `restriction S.val.toRingHom`. Here
  `S.val.toRingHom` is the actual inclusion of S into A.
- `coefficient_balanced` proves, for an ordinary S-module M, `c : k`, `a : A`
  and `m : M`:
  `algebraMap k A c • tmul S.val.toRingHom M a m =
  tmul S.val.toRingHom M a ((algebraMap k S c) • m)`.
  The left side uses the constructed residual action (`module`) on the
  constructed quotient. The proof combines `smul_tmul`, centrality of
  `algebraMap k A c` (`Algebra.commutes`), the compatibility
  `S.val (algebraMap k S c) = algebraMap k A c`, and `tmul_balanced`.
  The coefficient action on M here is the S-action transported through
  `algebraMap k S`. Nothing is asserted about any other k-action M may carry.

The source example is the case k = ℂ.

### Development checks

The file ends with `example`s that check the declarations elaborate in these
cases:

- `functor` at universe assignments (uB, uA, uM) = (2, 0, 1) and (0, 1, 0).
- `tensorMap` with input carrier in `Type 2` and output carrier in `Type`.
- `restriction` at carrier level 2 with rings in `Type 1` and `Type`.
- `functor (Int.castRingHom PUnit)`, a noninjective homomorphism onto the zero
  ring.
- `subalgebraFunctor S` for an arbitrary `S : Subalgebra ℤ (Module.End ℤ (ℤ × ℤ))`.
  This ring is the 2×2 integer matrices, which is not commutative. The file
  does not prove noncommutativity. The example only checks that no
  commutativity hypothesis is required.

## Scope

This unit gives only definitions and their intrinsic laws. It does not state
or prove:

- the source's θ and σ maps;
- the Hom equivalence, its naturality, or the inverse identities;
- the unit η and counit ε;
- the triangle identities;
- any comparison with the source's two-variable Hom-adjunction predicate.

Those remain separate obligations. No completion of Appendix A or of the book
is claimed.

## Dependencies

The unit imports the published Library modules
`Langlands.Algebra.NonUnitalBimoduleTensor` and
`Langlands.Algebra.NonUnitalModuleRestrictScalars`, plus Mathlib
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` and
`Mathlib.Algebra.Algebra.Subalgebra.Basic`. The pinned Mathlib commit is
`5ed2965256430c3649e86755f9576b54eca72435`, in Lean environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

Mathlib's native scalar extension `ModuleCat.extendScalars` requires
commutative rings at this version. So this unit builds the extension from the
Library's balanced quotient and residual action instead, which keeps A and B
possibly noncommutative.
