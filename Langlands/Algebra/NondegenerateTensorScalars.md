# Canonical scalars on balanced tensors of original nondegenerate modules

This module implements the tensor assertion in Renard, *Représentations des
groupes réductifs p-adiques*, version dated 9 July 2026, I.2.1, printed page 14 /
PDF page 20. It builds a coefficient-module structure on the published original
balanced tensor of a right and a left nondegenerate module. It then identifies
that tensor with an explicit quotient of the coefficient tensor of the two
canonically scalar-equipped factors. The exact complex case is the `complex…`
family of declarations. The general declarations are an internal generalization
to a commutative coefficient ring `k`. All declarations below are in
`Langlands.Algebra.NondegenerateTensorScalars`. In this file, "right factor"
means the right module `X`, given by an original `Aᵐᵒᵖ`-action. "Left factor"
means the left module `Y`.

## Sources and scope

The governing source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, content SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Its conventions, printed pages 5–7 / PDF pages 11–13, allow an associative,
possibly noncommutative and nonunital complex algebra. Modules there are abelian
groups with an associative distributive action. The same pages give the
idempotented and nondegenerate conditions. I.2.1 first gives every nondegenerate
`A`-module the complex structure `λm := (λe)·m` for any idempotent `e` with
`e·m = m`. That construction is the published `NondegenerateScalars.module`. The
passage then states that for a right module `X` and a left module `Y`, both
nondegenerate, "le produit tensoriel `X ⊗_A Y` hérite d'une structure d'espace
vectoriel et `X ⊗_A Y` est un quotient de `X ⊗_ℂ Y`". No proof is given. This
module formalizes exactly that sentence:

* the inherited complex vector-space structure is `complexModule`;
* the quotient assertion is `complexProjection` with
  `complexProjection_surjective`;
* the explicit kernel is `ker_complexProjection`;
* the quotient equivalence is `complexQuotientEquiv`.

The source sentence asserts only that the structure is inherited and that the
tensor is a quotient. The following are internal packaging of that assertion,
not displayed formulas of the book:

* the explicit relation submodule `K`;
* the two-sided equivalence with its inverse;
* the coefficient-linear universal lift `linearLift`;
* the induced linear maps `linearMap`.

The next paragraph of I.2.1 warns that a nonunital algebra gives no canonical
complex structure on an arbitrary `X ⊗_A Y`, and introduces `Ã = A ⊕ ℂ·1_A`. For
modules that are also vector spaces it then writes `X ⊗_Ã Y` as `X ⊗_A Y` modulo
the span of `λx ⊗ y − x ⊗ λy`, followed by (I.2.1.2). None of that is proved
here. This module does not form a tensor over `Unitization k A`. It does not
treat the arbitrary original tensor as a `k`-module. Its quotient equivalence is
not a proof of the unitized formula or of (I.2.1.2). That comparison needs the
actual original balanced tensor over a possibly noncommutative unitization and is
a separate successor. Mathlib's `TensorProduct` over a commutative ring cannot be
used directly as a tensor over a general noncommutative `Unitization k A`. The
following are also outside this module, each a separate successor:

* residual ring actions on the tensor;
* nondegeneracy of the tensor;
* associativity;
* the tensor–Hom adjunction;
* exactness;
* the forgetful and induction functors of I.2.2 (printed page 15 / PDF page 21).

The supplementary source is registered as `renard-2010-corrections-complements`,
content SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`. Its PDF
pages 1–2 give the early corrections, including a remark on tensor products at
the old Lemma I.3.2. Its PDF pages 18–19 correct the old printed-page-314
theorem by requiring an extra complex vector-space structure on the module,
using `Ã` as in I.2.1. These corrections concern arbitrary modules over a
nonunital algebra. They do not change the nondegenerate assertion formalized
here; the 2026 text governs. The original passages (PDF pages 11–13, 20, 21) and
the errata pages were read directly.

## Inputs and universes

The coefficient ring, algebra and carriers have independent universes:
`k : Type uK`, `A : Type uA`, `X : Type uX`, `Y : Type uY`. The inputs are

```lean
[CommRing k] [NonUnitalRing A] [Module k A]
[IsScalarTower k A A] [SMulCommClass k A A]
[AddCommGroup X] [AddCommGroup Y]
[NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]
hA : IsIdempotented A
hX : IsNondegenerate Aᵐᵒᵖ X
hY : IsNondegenerate A Y
```

The two compatibility classes express the two halves of coefficient
bilinearity of multiplication in `A`. A right action of `a : A` is the original
action of `op a`. There is no prior `Module k X` or `Module k Y` input, and no
compatibility proof on either factor. Linear-endomorphism realizations, unit
laws on `A`, commutativity of `A`, nontriviality, dimension and finiteness are
not inputs either.

The tensor is exactly the published `NonUnitalModuleTensor.Tensor A X Y`. Its
carrier is `Type (max uX uY)`, independent of `uK` and `uA`. Its additive group
is the published one, and `tmul`, `lift`, `hom_ext` and `map` are the published
ones. A commutative ring, rather than the semiring allowed by
`NondegenerateScalars`, is needed because the construction forms the quotient
module of `X ⊗[k] Y` by a submodule.

The factor scalars are the published ones, unchanged:

* `rightModule k hA hX := NondegenerateScalars.module k hA.op hX`, on `X` over
  `Aᵐᵒᵖ`;
* `leftModule k hA hY := NondegenerateScalars.module k hA hY`, on `Y`.

`rightModule_eq` and `leftModule_eq` record this by `rfl`. `Aᵐᵒᵖ` carries
Mathlib's inherited `Module k Aᵐᵒᵖ`. The published construction on `Aᵐᵒᵖ`
needs the two compatibility classes over the opposite ring. These are the
theorems `opIsScalarTower` (from `SMulCommClass k A A`) and `opSMulCommClass`
(from `IsScalarTower k A A`), installed only as local instances.
`IsIdempotented.op` comes from the published `NonUnitalModule` file. All module
structures are named declarations installed locally with `letI`; this module
declares no global instances. `isNondegenerate_of_subsingleton` is a small
helper: on a subsingleton group the zero idempotent fixes every vector.

## The scalar module on the original tensor

The construction is first done generically in the section `Compatible`. That
section takes any coefficient module on `Y` and a proof that it commutes with
the original action, as named instance arguments `instY` and `commY`.

* `compatibleScalarHom k A Y c` is `y ↦ c • y` as an actual
  `NonUnitalModuleHom A Y Y`. Intertwining is `smul_comm`.
* `compatibleScalarEnd k A X Y c` is the published
  `NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X)
  (compatibleScalarHom k A Y c)`, an additive endomorphism of the tensor.
* `compatibleModule` is the `Module k (Tensor A X Y)` with multiplication
  `c • t := compatibleScalarEnd k A X Y c t`, on the retained additive group.

`compatibleModule` proves its laws intrinsically:

* `smul_zero` and `smul_add` are additivity of the endomorphism.
* `one_smul`, `mul_smul`, `add_smul` and `zero_smul` come from the equalities
  of endomorphisms `compatibleScalarEnd_one`, `_mul`, `_add` and `_zero`. Each
  is proved by the published `hom_ext` on pure tensors, using the corresponding
  law on `Y` together with `tmul_add` / `tmul_zero` for the sum and zero cases.

`linearOfPure` turns an additive map out of the tensor into a linear map. Its
hypothesis is that the map commutes with `y ↦ c • y` on pure tensors. It
upgrades that pure-tensor identity to an equality of additive maps by `hom_ext`.
`linearOfPure_toAddMonoidHom` records that the underlying additive map is
unchanged. `compatible_linear_hom_ext` shows that linear maps out of the tensor
are determined by their pure values.

The canonical structure applies this to the published scalars on `Y`:

* `scalarHom k hA hY c` is `compatibleScalarHom` with
  `instY := leftModule k hA hY` and
  `commY := NondegenerateScalars.smulCommClass k hA hY`. The intertwiner
  `y ↦ c • y` is therefore built from the published proved compatibility
  `c • (a • y) = a • (c • y)`, not assumed.
* `scalarEnd k A X Y hA hY c` is
  `NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (scalarHom k hA hY c)`.
* `module k A X Y hA hY : Module k (Tensor A X Y)` is the corresponding
  `compatibleModule` (`module_eq`, `rfl`).

`smul_def` gives `c • t = scalarEnd … c t`. `toAddMonoidHom_smul` exposes the
whole additive scalar endomorphism `DistribSMul.toAddMonoidHom _ c` as that
published tensor map. `smul_tmul_right` gives `c • tmul x y = tmul x (c • y)`.

As the contract permits, this is the stronger one-sided construction: `module`
needs only `hA` and `hY`. The published interface below covers the two-factor
nondegenerate setting, and every result involving scalars on `X` takes `hX`.

## Moving scalars across the tensor: a fixing idempotent and balancing

`tmul_smul_left_eq` proves `tmul (c • x) y = tmul x (c • y)` for the published
canonical scalars on both factors. Let `e : Idempotent Aᵐᵒᵖ` be a fixer of `x`
from `hX x`, and put `ε = unop e`, so `op ε • x = x`.

1. The published fixer formula `NondegenerateScalars.smul_eq` on `X` over `Aᵐᵒᵖ`
   gives `c • x = op (c • ε) • x`.
2. The original balancing law `NonUnitalModuleTensor.tmul_balanced` gives
   `tmul (op (c • ε) • x) y = tmul x ((c • ε) • y)`.
3. The published compatibility `NondegenerateScalars.smul_action` on `Y` gives
   `(c • ε) • y = c • (ε • y)`. So the term is
   `tmul x (c • (ε • y)) = scalarEnd c (tmul x (ε • y))`.
4. Balancing again gives `tmul x (ε • y) = tmul (op ε • x) y = tmul x y`.
5. Finally `scalarEnd c (tmul x y) = tmul x (c • y)`.

Then:

* `smul_tmul_left` gives `c • tmul x y = tmul (c • x) y`.
* `smul_tmul_function` states the full two-variable formulas as equalities of
  functions of `x` and `y`:

  ```text
  c • tmul A X Y x y = tmul A X Y (c • x) y = tmul A X Y x (c • y).
  ```

* `map_rightScalarHom_id` shows that the same endomorphism is also the published
  map of `x ↦ c • x` (as `rightScalarHom`, an original right intertwiner) and
  `id_Y`.

## The bilinear pure map and the projection

* `bilinear k A X Y hA hX hY : X →ₗ[k] Y →ₗ[k] Tensor A X Y` is `LinearMap.mk₂`
  applied to the published `tmul`. Additivity is the published `add_tmul` and
  `tmul_add`. Linearity in `x` is `tmul_smul_left_eq`, and linearity in `y`
  holds by definition.
* `bilinear_apply` and `bilinear_function` give its pure values and its
  equality with the published `tmul` function.
* `toBiadditive_bilinear` shows that its complete underlying biadditive map is
  the published `NonUnitalModuleTensor.biadditive`. Here `toBiadditive` is the
  underlying biadditive map of a bilinear map.
* `coefficientProjection` is `π := TensorProduct.lift (bilinear …)`
  (`coefficientProjection_eq_lift`), with pure formula
  `coefficientProjection_tmul`.
* `mk_compr₂_coefficientProjection` is the whole-map factorization
  `(TensorProduct.mk k X Y).compr₂ π = bilinear …`.
* `coefficientProjection_surjective` uses the original quotient. Every element
  of the tensor is the published `projection` of some element of `X ⊗[ℤ] Y`, by
  the published `projection_surjective`. Induction on that integer tensor (pure
  tensors and sums) produces a preimage under `π`.

## The coefficient relations and the quotient equivalence

`coefficientRelations k A X Y hA hX hY` is the actual span

```text
K = Submodule.span k
      { (op a • x) ⊗ₜ[k] y - x ⊗ₜ[k] (a • y) | a : A, x : X, y : Y }
```

inside `X ⊗[k] Y`, formed with the canonical factor modules
(`coefficientRelations_eq_span`, `rfl`; `generator_mem_coefficientRelations`).

* Forward map. `coefficientRelations_le_ker` sends each generator to zero by
  original balancing. `quotientToTensor` is `K.liftQ π`.
* Inverse. `toQuotientBiadditive` is `x ↦ y ↦ class of x ⊗ₜ[k] y`, as an actual
  biadditive map. It is balanced (`toQuotientBiadditive_balanced`) because each
  balancing difference is a generator of `K`. `tensorToQuotient` is the
  published original lift of this map, made linear by `canonicalLinearOfPure`
  (`linearOfPure` for the canonical structure). On pure tensors,
  `x ⊗ₜ (c • y) = c • (x ⊗ₜ y)` (`TensorProduct.tmul_smul`) and
  `Submodule.Quotient.mk_smul` give the needed scalar identity.
* Both composites are identities.
  `quotientToTensor_comp_tensorToQuotient` follows from the published `hom_ext`
  on additive maps. `tensorToQuotient_comp_quotientToTensor` follows from
  `Submodule.linearMap_qext` and `TensorProduct.ext'`. In both cases the pure
  values agree by definition.
* `quotientEquiv k A X Y hA hX hY : ((X ⊗[k] Y) ⧸ K) ≃ₗ[k] Tensor A X Y` is
  `LinearEquiv.ofLinearMap` of these two maps.

Its interface:

* pure values on both sides: `quotientEquiv_mk_tmul` (the class of
  `x ⊗ₜ[k] y` goes to `tmul x y`) and `quotientEquiv_symm_tmul` (`tmul x y` goes
  back to that class);
* both linear maps: `quotientEquiv_toLinearMap` and
  `quotientEquiv_symm_toLinearMap`;
* both complete additive maps: `quotientEquiv_toAddMonoidHom` (the quotient
  lift of `π`) and `quotientEquiv_symm_toAddMonoidHom` (the published original
  `NonUnitalModuleTensor.lift` of `toQuotientBiadditive`);
* both whole-map inverse identities: `quotientEquiv_symm_comp` and
  `quotientEquiv_comp_symm`;
* `coefficientProjection_eq_comp_mkQ`: `π` equals the forward map composed with
  `K.mkQ` (`Submodule.liftQ_mkQ`);
* `ker_coefficientProjection`: `ker π = K`, deduced from that factorization by
  `LinearEquiv.ker_comp` and `Submodule.ker_mkQ`.

## Coefficient-linear universal lift

Take any `Z : Type uZ` with an `AddCommGroup Z` and a supplied `Module k Z`. No
`A`-action on `Z` is used. Take any actual bilinear
`b : X →ₗ[k] Y →ₗ[k] Z` for the canonical factor modules, with
`hb : ∀ a x y, b (op a • x) y = b x (a • y)`.

* `linearLift k A X Y hA hX hY b hb` is the published
  `NonUnitalModuleTensor.lift A (toBiadditive b) hb`, made linear by
  `canonicalLinearOfPure` using linearity of `b x`.
* `linearLift_toAddMonoidHom` gives its complete additive map.
* `linearLift_tmul` gives its pure formula `tmul x y ↦ b x y`.
* `bilinear_compr₂_linearLift` gives the whole-map factorization through
  `bilinear`.
* `linearLift_unique` gives uniqueness: any linear `f` with the same pure values
  equals it, as an equality of complete linear maps. This follows from
  `linear_hom_ext`.

No further universal-equivalence packaging is provided.

## Coefficient-linear induced maps

Take independently sized original factors `X' : Type uX'` and `Y' : Type uY'`,
and original intertwiners `f : NonUnitalModuleHom Aᵐᵒᵖ X X'` and
`g : NonUnitalModuleHom A Y Y'`.

* `linearMap k A hA hY hY' f g` is precisely the published
  `NonUnitalModuleTensor.map A f g`, made linear between the canonical tensor
  modules by `canonicalLinearOfPure`. The pure identity
  `map (tmul x (c • y)) = c • tmul (f x) (g y)` comes from the published
  automatic linearity `NondegenerateScalars.map_smul` of `g`. It is therefore
  proved from the original intertwiner and the canonical scalar constructions.
  Like `module`, this needs only `hA`, `hY` and `hY'`.
* `linearMap_toAddMonoidHom` gives its complete additive map, and
  `linearMap_tmul` its pure formula.
* `linearMap_id` and `linearMap_comp` give the identity and composition laws,
  with a third pair `X'' : Type uX''`, `Y'' : Type uY''`. They are deduced from
  the published `map_id` and `map_comp`.
* `linearMap_comp_coefficientProjection` is the naturality square with `π`. It
  takes `hX`, `hX'` and `hY'`. The other side is
  `TensorProduct.map (NondegenerateScalars.toLinearMap k hA.op hX hX' f)
  (NondegenerateScalars.toLinearMap k hA hY hY' g)`, the coefficient tensor map
  of the published canonical linear refinements of `f` and `g`. It is checked
  on pure tensors with `TensorProduct.ext'`.

No categorical tensor functor is constructed.

## Renard's complex case

The sections `Complex` and `ComplexMaps` give the exact specialization `k = ℂ`.
Algebra and carrier universes stay arbitrary and independent, the algebra may be
nonunital and noncommutative, and the dimension is unrestricted.

* `complexRightModule` and `complexLeftModule` are the factor modules.
  `complexRightModule_eq` and `complexLeftModule_eq` identify them with the
  published `NondegenerateScalars.complexModule hA.op hX` and
  `NondegenerateScalars.complexModule hA hY`.
* `complexModule` is the tensor structure (`complexModule_eq`).
* `complex_toAddMonoidHom_smul`, `complex_smul_tmul_right`,
  `complex_smul_tmul_left` and `complex_smul_tmul_function` give the scalar
  endomorphism and the formulas.
* `complexBilinear` (`_apply`) and `toBiadditive_complexBilinear` give the
  bilinear pure map.
* `complexProjection` (`_eq_lift`, `_tmul`, `_surjective`) is the projection.
* `complexRelations` (`_eq_span`) is `K`.
* `complexQuotientEquiv` is the equivalence, with:
  * pure values `_mk_tmul` and `_symm_tmul`;
  * inverse identities `_symm_comp` and `_comp_symm`;
  * complete additive maps `_toAddMonoidHom` and `_symm_toAddMonoidHom`.
* `complexProjection_eq_comp_mkQ` and `ker_complexProjection` give the
  factorization through `mkQ` and the kernel.
* `complexLinearLift` (`_toAddMonoidHom`, `_tmul`, `_unique`) is the linear
  universal lift.
* `complexLinearMap` (`_toAddMonoidHom`, `_tmul`, `_id`, `_comp`) gives the
  induced maps.
* `complexLinearMap_comp_complexProjection` is naturality against the published
  `NondegenerateScalars.complexToLinearMap`.

Each is the general declaration at `ℂ`.

## Checks included in the file

* **Unapplied type checks.** Each check is
  `example : ∀ …, T := @name` with the complete binder list in declaration
  order. They cover the named scalar structure and endomorphism (`module`,
  `scalarEnd`, `smul_def`, `toAddMonoidHom_smul`, `smul_tmul_function`), the
  bilinear map and its biadditive map, the projection and its formulas and
  surjectivity, `K` and its span equality, the quotient equivalence with both
  pure formulas, both complete additive maps and both inverse identities, the
  `mkQ` factorization and the kernel, and the linear lift and induced maps with
  their laws. The checks run for general `k` and for `ℂ`. Each is done at
  arbitrary universe variables and at two unequal fixed assignments, one in
  each direction. For general `k` these are
  `(uK, uA, uX, uY, uZ, uX', uY', uX'', uY'') = (1, 0, 1, 0, 1, 0, 1, 0, 1)` and
  `(0, 1, 0, 1, 0, 1, 0, 1, 0)`. For `ℂ` the same alternating patterns are used
  on `(uA, uX, uY, uZ, uX', uY', uX'', uY'')`, starting with `0` and with `1`.
* **Competing structures.** With competing `Module k X`, `Module k Y` and
  `Module k (Tensor A X Y)` instances in context, `rfl` checks show that the
  installed structures are exactly the published factor modules and the
  constructed tensor module. They also show that `c • t` is the published
  tensor map of `id_X` and `y ↦ c • y`, and that the formulas, bilinear map, `K`
  and quotient equivalence elaborate against these choices. The same is checked
  for `ℂ`. Further sections pass the original choices explicitly to the
  constructions while a competing instance is in scope: a competing target
  `Module k Z` in `linearLift`; a competing `CommRing k`; a competing
  `NonUnitalRing A` and `Module k A`; competing factor groups; competing
  original actions.
* **Subsingleton factors.** If `X` or `Y` is a subsingleton, it is nondegenerate.
  The tensor and the quotient are then subsingletons and `K = ⊤`. Over a
  subsingleton algebra with subsingleton factors the construction still
  applies.
* **Regular integer example.** Take `A = k = ℤ` and `X = Y = ℤ`, with the right
  regular action `NonUnitalModule.ofModule ℤᵐᵒᵖ ℤ` and the left regular action
  `NonUnitalModule.ofModule ℤ ℤ`. Both are nondegenerate, with the unit fixing
  every vector, and `hA = IsIdempotented.of_ring ℤ`.
  * `tmul 1 1 ≠ 0`, because the published lift of the balanced map
    `(x, y) ↦ x * y` sends it to `1`.
  * With the canonical scalar action installed, `c • tmul 1 1 = tmul c 1` and
    `c • tmul 1 1 = tmul 1 c`. Both factor scalars are computed from
    `NondegenerateScalars.smul_eq` with the unit idempotent.
  * For `k = ℤ`, `c • t` otherwise elaborates to the additive group's integer
    action, so the example installs the canonical scalar action explicitly.
    Separate examples prove that this canonical module agrees with
    `AddCommGroup.toIntModule`, as all integer modules on a group do.

  No zero action on a nonzero factor is claimed to be nondegenerate.

Development checks built the module with no errors or warnings. Inspection of
`quotientEquiv`, which depends on the scalar module, the bilinear map, the
projection, `K` and both directions of the equivalence, reports only Lean's
standard axioms `propext`, `Classical.choice` and `Quot.sound`. These checks are separate
from independent review and publication.
