# Tensors over the unitization and the additive scalar comparison

Authors: Worker 1088 read the cited passages, designed and implemented the
construction sections of `Langlands/Algebra/CompatibleUnitizationTensor.lean`
(namespace `Langlands.Algebra.CompatibleUnitizationTensor`) and wrote this note.
Worker 803 independently read the same passages and wrote the examples section.
The task `fc080bdb-06d7-432a-aa3f-0f72928470f2` was published by Worker 6 as a
definition prerequisite of whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

For a `k`-algebra `A` acting compatibly on the right of `X` and on the left of
`Y`, the module builds

1. the unital action of `U = Unitization k A` on `Y` and the unital action of
   `Uᵐᵒᵖ` on `X`, with their formulas, restrictions, unit laws and coefficient
   compatibility;
2. the actual tensors `TA = NonUnitalModuleTensor.Tensor A X Y` and
   `TU = NonUnitalModuleTensor.Tensor U X Y`, the balancing of the `TU` pure map
   for the original actions and for the scalars, the identification of
   `U`-balancing with these two equations, and the universal additive lift
   from `TU`;
3. the comparison `q : TA →+ TU` and its surjectivity;
4. the integer submodule `H ⊆ TA` spanned by the scalar-balancing differences,
   the additive quotient `Q = TA ⧸ H`, the inclusion `H ≤ ker q` and the
   descended map `qbar : Q →+ TU`.

The kernel equality `H = ker q` and the bijectivity of `qbar` are **not** stated
or proved here. They are left to the next statement/proof unit and are not
hypotheses of anything in this module. No `Module k` (and no complex vector
space structure) is constructed on `TA`, `TU` or `Q`.

The module imports the published `Langlands.Algebra.CompatibleUnitization`
(its `module`, `inr_smul`, `inl_smul`, `one_smul`, `isScalarTower`,
`smulCommClass`), `Langlands.Algebra.NonUnitalModuleTensor` (`Tensor`,
`addCommGroup`, `tmul`, `biadditive`, `tmul_balanced`, `IsBalanced`, `lift`,
`lift_unique`, `hom_ext`, `projection`, `projection_surjective`,
`integerLift`) and, through them, `NonUnitalModule.toLinearEndHom` and
`NonUnitalModule.ofModule`.

## Original source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**: the registered source
`renard-2026-representations-groupes-reductifs-padiques`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed page = PDF page minus 6. Passages read:

- Notation and conventions, printed pp. 5–7 / PDF11–13: rings are not assumed
  unital, modules over a unital ring are not assumed unital a priori, and right
  modules are used alongside left modules.
- I.2.1, printed p. 14 / PDF20. For a complex algebra `A` without unit there is
  no canonical complex vector space structure on `Hom_A(X,Y)` or on `X ⊗_A Y`,
  "même lorsque X et Y sont des espaces vectoriels". Renard introduces the
  unital algebra `Ã = A ⊕ ℂ·1_A`. If `X` and `Y` are `A`-modules and also
  complex vector spaces, "ils deviennent naturellement des Ã-modules
  unitaires", and

  ```text
  X ⊗_Ã Y = X ⊗_A Y / Vect({λx ⊗ y − x ⊗ λy, x ∈ X, y ∈ Y, λ ∈ ℂ}).
  ```

  Under the idempotented and nondegenerate hypotheses this becomes (I.2.1.2),
  `X ⊗_Ã Y = X ⊗_A Y`.
- I.2.2, printed p. 15 / PDF21: the associativity formulas use `⊗_R̃` for the
  unitization of an arbitrary complex algebra `R`, so the tensor over the
  unitization is used for general original modules.

Supplementary errata: the registered `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF1–2 and PDF18–19 were read. Its item for the 2010 Schur lemma asks that the
module be a complex vector space and that one reduce to `Ã` as in I.2.1; it
contains no correction of the I.2.1 tensor formula. No Renard errata note was
present in the project notes tree. No source error is claimed here.

### Hypotheses and generalization

The source works over `ℂ`. Here `k` is any commutative ring (`CommRing k`),
`A` a `NonUnitalRing` with `Module k A`, `IsScalarTower k A A` and
`SMulCommClass k A A`, and `X`, `Y` are `AddCommGroup`s with `Module k`
structures and original actions `NonUnitalModule Aᵐᵒᵖ X` and
`NonUnitalModule A Y` (the right action of `a` is `op a • x`). The
specialization `k = ℂ` is exactly the source's setting.

"Ils deviennent naturellement des Ã-modules unitaires" needs the scalar action
to be compatible with the algebra action: `λ(a·m) = (λa)·m = a·(λm)`, as in
(I.2.1.1). The source leaves this implicit; here it is the explicit hypothesis
`IsScalarTower k A Y` and `SMulCommClass k A Y` on `Y`, and
`IsScalarTower k Aᵐᵒᵖ X` and `SMulCommClass k Aᵐᵒᵖ X` on `X`, with the
inherited `k`-action on `Aᵐᵒᵖ`. Nothing else is assumed: no unit law for the
original actions, nondegeneracy, idempotents, commutativity of `A`,
nontriviality, dimension or finiteness.

## The unitized actions

`leftEndHom k A Y` and `rightEndHom k A X` are the published
`NonUnitalModule.toLinearEndHom k` for the original actions of `A` on `Y` and of
`Aᵐᵒᵖ` on `X`: actual non-unital `k`-algebra homomorphisms into
`Module.End k`.

`leftModule k A Y : Module (Unitization k A) Y` is precisely
`CompatibleUnitization.module (leftEndHom k A Y)` (`leftModule_eq`), so
`u • y = u.fst • y + u.snd • y` (`left_smul_eq`, `left_smul_function`).

**Handedness adapter.** `(Unitization k A)ᵐᵒᵖ` is not definitionally
`Unitization k Aᵐᵒᵖ`. `opRingEquiv k A : (Unitization k A)ᵐᵒᵖ ≃+* Unitization k Aᵐᵒᵖ`
is the genuine ring equivalence `op u ↦ (u.fst, op u.snd)`, with inverse
`v ↦ op (v.fst, v.snd.unop)`. The coordinate formulas are `rfl`
(`opRingEquiv_fst`, `_snd`, `_symm_fst`, `_symm_snd`, `_function`,
`_symm_function`). Additivity is `rfl`; multiplicativity compares the first
coordinates by commutativity of `k`, and the second coordinates by `op_add`,
`op_smul`, `op_mul` and one commutation of summands. Only the multiplications
and additions of `k` and `A` enter.

The `k`-algebra structure that `CompatibleUnitization` needs on `Aᵐᵒᵖ` uses two
named theorems: `opIsScalarTower k A : IsScalarTower k Aᵐᵒᵖ Aᵐᵒᵖ` (from
`SMulCommClass k A A`, i.e. `mul_smul_comm`) and
`opSMulCommClass k A : SMulCommClass k Aᵐᵒᵖ Aᵐᵒᵖ` (from `IsScalarTower k A A`,
i.e. `smul_mul_assoc`). They are not global instances; they are used with
`haveI` inside the definition below.

`rightModule k A X : Module (Unitization k A)ᵐᵒᵖ X` is
`Module.compHom X (opRingEquiv k A).toRingHom` of the published
`CompatibleUnitization.module (rightEndHom k A X)`. Hence, by `rfl`,

```text
(op u) • x = u.fst • x + (op u.snd) • x        (right_smul_eq, right_smul_function).
```

For both actions the module exposes the restriction to `inr`, which recovers
the given original action (`left_inr_smul`, `right_inr_smul`), the restriction
to `inl`, which is the given scalar action (`left_inl_smul`, `right_inl_smul`),
the unit law (`left_one_smul`, `right_one_smul`), and coefficient
compatibility (`left_isScalarTower`, `left_smulCommClass`,
`right_isScalarTower`, `right_smulCommClass`). The left ones are the published
`CompatibleUnitization` lemmas; the right ones are proved from
`right_smul_eq` and the inherited `Unitization`/`MulOpposite` coordinate
lemmas (`fst_inr`, `snd_inl`, `op_zero`, `NonUnitalModule.zero_smul`,
`smul_assoc`, `smul_comm`).

`leftNonUnitalModule k A Y` and `rightNonUnitalModule k A X` are the named
ambient adapters `NonUnitalModule.ofModule` of these two unital modules, with
the same action (`leftNonUnitalModule_smul`, `rightNonUnitalModule_smul`, both
`rfl`). All six of these structures are definitions, not global instances, so
they never compete with the original actions.

## The two tensors

`TA` is the published `NonUnitalModuleTensor.Tensor A X Y` for the original
actions. `UnitizedTensor k A X Y` (`TU`) is the abbreviation for
`NonUnitalModuleTensor.Tensor (Unitization k A) X Y` with the actions
`rightNonUnitalModule k A X` and `leftNonUnitalModule k A Y`
(`unitizedTensor_eq` displays them). Both lie in `Type (max uX uY)`, independent
of `uK` and `uA`. Their additive groups are the published inherited ones
(`unitizedTensor_addCommGroup_eq`, `rfl`); no replacement tensor or additive
structure is supplied. Inside the `Tensors` and `Comparison` sections the two
adapters are local instances only.

`unitizedTmul` and `unitizedBiadditive` are the published `tmul` and
`biadditive` over the unitization (`unitizedTmul_function`,
`unitizedBiadditive_apply`, `unitizedBiadditive_function`).
`unitizedTmul_balanced` is the published `tmul_balanced` over `U` for the
constructed actions. Specializing it at `inr a` and `inl c` and rewriting with
the restriction lemmas gives

```text
tmul_U ((op a) • x) y = tmul_U x (a • y)     (unitizedTmul_original)
tmul_U (c • x) y = tmul_U x (c • y)          (unitizedTmul_scalar).
```

For an independent `Z : Type uZ` with `AddCommGroup Z` and an actual
biadditive `b : X →+ Y →+ Z`, `IsScalarBalanced k b` is the Prop
`∀ c x y, b (c • x) y = b x (c • y)`. `isBalanced_unitization_iff` proves

```text
IsBalanced (Unitization k A) b ↔ IsBalanced A b ∧ IsScalarBalanced k b.
```

Forward: evaluate at `inr a` and `inl c` and use the restriction lemmas.
Backward: expand `op u • x` and `u • y` by the two action formulas and use the
additivity of `b` in each variable. No action or coefficient module on `Z` is
used.

`unitizedLift k A b ha hc : TU →+ Z` is the published
`NonUnitalModuleTensor.lift (Unitization k A) b` applied to the `U`-balancing
obtained from `ha` and `hc` by this equivalence (`unitizedLift_eq`). It
composes with the published projection to `integerLift b`
(`unitizedLift_comp_projection`), has pure values `b x y` (`unitizedLift_tmul`,
`unitizedLift_pure_function`), and is the unique additive map with these values
(`unitizedLift_unique`, equality of whole additive maps, from the published
`lift_unique`). `unitizedHom_ext` is the published `hom_ext` over `U`. This is
an interface to the constructed tensor, not an assumed universal property.

## The comparison and the scalar quotient

`unitizedBiadditive_isBalanced` restates `unitizedTmul_original` as
`IsBalanced A (unitizedBiadditive k A X Y)`. `comparison k A X Y : TA →+ TU`
(`q`) is precisely `NonUnitalModuleTensor.lift A (unitizedBiadditive k A X Y)`
with that proof (`comparison_eq`). Its pure values are `unitizedTmul`
(`comparison_tmul`, `comparison_pure_function`). Composed with the published
projection of `TA` it is `integerLift (unitizedBiadditive k A X Y)`
(`comparison_comp_projection`), and this equals the published projection of `TU`
(`comparison_comp_projection_eq`, by `TensorProduct.ext'` on the integer
tensor after `AddMonoidHom.toIntLinearMap_injective`).

`comparison_surjective`: every element of `TU` is the projection of an integer
tensor (`projection_surjective`), and by `TensorProduct.inductionOn` on that
integer tensor (whose cases in this Mathlib version are pure tensors and
sums), its projection is a value of `q`: the projection of `x ⊗ y` is
`q (tmul_A x y)`, and sums are handled by additivity of `q` and of the
projection.

`scalarRelations k A X Y` (`H`) is

```text
Submodule.span ℤ (Set.range fun (c, x, y) => tmul_A (c • x) y − tmul_A x (c • y)),
```

a `Submodule ℤ TA`. The scalars inside the generators are the given `k`-actions
on `X` and `Y`; the ambient integer action on `TA` is `AddCommGroup.toIntModule`
of its inherited additive group. `scalarDifference_mem` records that each
generator lies in `H`.

**Integer-span convention.** The source writes `Vect` of these differences,
the complex span, although it has just observed that the original tensor has
no canonical complex vector space structure. This module chooses no such
structure: `H` is the integer span, and `ScalarQuotient k A X Y` (`Q`) is the
abbreviation for `TA ⧸ H` with its inherited additive group. It is not
asserted that `Vect` on `TA` is already defined, nor that `qbar` is an
isomorphism. A later scalar refinement may choose one-sided coefficient
scalars on `TA` and prove that their span has the same underlying additive
subgroup.

`scalarRelations_le_ker` proves `H ≤ ker q.toIntLinearMap` by `Submodule.span_le`:
`q` sends each generator to `tmul_U (c • x) y − tmul_U x (c • y) = 0` by
`unitizedTmul_scalar`. `descendedComparison k A X Y : Q →+ TU` (`qbar`) is
`(H.liftQ q.toIntLinearMap _).toAddMonoidHom` (`descendedComparison_eq`). Its
pure values are `qbar (mk t) = q t` (`descendedComparison_mk`) and
`qbar (mk (tmul_A x y)) = tmul_U x y` (`descendedComparison_mk_tmul`), and
`qbar.comp H.mkQ.toAddMonoidHom = q` as whole additive maps
(`descendedComparison_comp_mkQ`); all three are `rfl`.

## Examples

The `Examples` section of the Lean file contains only `example`s and section-local
notations; it adds no declarations. Each item below is checked by Lean.

**The complex specialization.** With `k = ℂ` and the algebra, the two factors
and the target in independent universes `uA uX uY uZ`, the following elaborate
as complete types: the left and right unitized modules and their non-unital
adapters, `TU`, both balancing laws, `q` and `comparison_surjective`, `H`, `Q`,
`scalarRelations_le_ker`, `qbar` and `descendedComparison_comp_mkQ`, the
balancing equivalence `isBalanced_unitization_iff` and `unitizedLift`.

**Complete unapplied interfaces.** The complete unapplied types of
`leftModule`, `rightModule`, `leftNonUnitalModule`, `rightNonUnitalModule`,
`UnitizedTensor`, `comparison`, `scalarRelations`, `ScalarQuotient`,
`descendedComparison`, `isBalanced_unitization_iff` and `unitizedLift` are
stated at arbitrary universes `uK uA uX uY uZ`, and at the unequal choices
`(uK, uA, uX, uY, uZ) = (0, 1, 0, 1, 0)` and `(1, 0, 1, 0, 1)`.

**Explicit choices under competing structures.** Competing coefficient modules
`Module k X`, `Module k Y` and competing original actions of `A` on `X` and `Y`
are placed in scope after the selected ones. `rfl` then shows that the
explicitly passed structures are the ones used: they enter the left and right
unitized actions (`u • y = u.fst • y + u.snd • y`, and similarly on the right),
the restrictions of the adapters along `inr`, the carrier of `TU`, the
generators of `H`, and the value of `q` on pure tensors; `qbar` elaborates as a
complete additive map for these selected structures. Typed checks show that
`q`, `qbar` and `unitizedLift` accept explicitly selected additive groups on
the factors when competing ones are in scope, and that `q`, `qbar` and
`isBalanced_unitization_iff` accept an explicitly selected coefficient ring and
algebra when competing ones are in scope. The integer scalars on
`TA` are `AddCommGroup.toIntModule` of its inherited additive group (`rfl`),
and `H` is a submodule for these scalars even when a competing `Module ℤ TA` is
in scope.

**Subsingleton factors.** If `X` or `Y` is a subsingleton, then `TA`, `TU`
and `Q` are subsingletons, `H = ⊤`, and `qbar` is bijective. Every element of
`TA` is zero: it is the projection of an integer tensor
(`projection_surjective`), and `TensorProduct.inductionOn` reduces it to
`zero_tmul` or `tmul_zero` on pure tensors. `TU` and `Q` are then
subsingletons as images of `TA` under the surjections `q` and `mkQ`, and
`qbar` is surjective because `q` is.

**Zero original actions of `ℂ` on `ℂ`.** Take `k = A = X = Y = ℂ`, with
`NonUnitalModule.zero` as both original actions and multiplication as both
coefficient modules. Then:

- `inr 1` acts by `0` on both sides, and the unit `1` of the unitization acts
  by the identity on both sides, so the unitized actions are unital although
  the original ones are not.
- The relation `tmul_A (I • 1) 1 − tmul_A 1 (I • 1)` is nonzero in `TA`. The
  conjugate pairing `(x, y) ↦ conj x * y` is balanced for the zero actions,
  since both sides of the balancing law are `0`, and its published `lift`
  takes the value `conj I − I = −2I` on this relation.
- The relation lies in `H`, is killed by `q` (so `q` is not injective), and
  its class in `Q` is zero.
- `tmul_U 1 1 ≠ 0`, because `unitizedLift` of the multiplication pairing,
  which is balanced for the zero actions and `ℂ`-balanced, takes the value `1`
  on it.

This shows that `H` can be nonzero, so `TA` and `Q` can differ.
