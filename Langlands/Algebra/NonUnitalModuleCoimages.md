# Concrete categorical coimages of original nonunital-module morphisms

This module constructs the coimage of an actual morphism `f : M ⟶ N` in
`Langlands.Algebra.NonUnitalModuleCat A`, using the original stable kernel
and quotient action. All declarations are in
`Langlands.Algebra.NonUnitalModuleCat`. The inputs are exactly
`A : Type uA`, `[NonUnitalRing A]`, original objects
`M N : NonUnitalModuleCat.{uA, uM} A`, and `f`.

The ring can be noncommutative and nonunital. The construction includes zero
rings, zero carriers, and degenerate original actions, including the zero
action over a unital ring. It imposes no unit-action, idempotentedness,
nondegeneracy, scalar-field, nontriviality, or finiteness hypothesis. The ring
and carrier universes are independent.

## The quotient and its original maps

`concreteCoimage f` has the actual carrier

```lean
M ⧸ f.kernelSubmodule.toIntCompatible.toSubmodule
```

in `Type uM`, as recorded by `concreteCoimage_carrier`. It uses the existing
`quotientNonUnitalModule` action on this quotient. The integer-compatible
description is the canonical interpretation of the original additive group;
it retains the original `A`-action and the original morphisms.

`concreteCoimageπ f` is the existing `mkQNonUnitalModuleHom` projection.
`factorThruConcreteCoimage f` is obtained from the original map by
`LinearIntertwiner.liftQ` and `toNonUnitalModuleHom`. Their representative
formulas and the action formula are:

```text
concreteCoimageπ f (m) = [m]
factorThruConcreteCoimage f ([m]) = f(m)
a • [m] = [a • m].
```

These are `concreteCoimageπ_apply`,
`factorThruConcreteCoimage_apply_mk`, and `concreteCoimage_smul_mk`.
Here application abbreviates application of the original morphism's
`toAddMonoidHom`. `concreteCoimageπ_eq_zero_iff` identifies a zero coset with
membership in the existing `f.kernelSubmodule`;
`concreteCoimageπ_eq_zero_iff_map_eq_zero` identifies the same condition
with `f(m) = 0`.

`concreteCoimage_fac` proves that the projection followed by the descended
map is `f`. Every quotient element has a representative, proving
`concreteCoimageπ_surjective`. Evaluating equal composites on representatives
proves the categorical instance `concreteCoimageπ_epi`. For
`factorThruConcreteCoimage_injective`, quotient induction reduces equality
of two descended values to equality of `f(m)` and `f(n)`. Additivity puts
`m - n` in the original kernel, giving equality of cosets. The published
original mono/injective criterion then supplies
`factorThruConcreteCoimage_mono`.

## Explicit cokernel universal property

`concreteKernelι_comp_concreteCoimageπ` proves that the original concrete
kernel inclusion followed by the projection is zero. Given any original
map `g : M ⟶ P` and `h : concreteKernelι f ≫ g = 0`,
`kernel_le_ker_of_concreteKernelι_comp_eq_zero` evaluates `h` on kernel
vectors to show that `g` kills the stable kernel.

`concreteCoimageDesc f g h` then uses the published `liftQ` to construct the
original morphism from the quotient to `P`.
`concreteCoimageDesc_apply_mk` gives `[m] ↦ g(m)`;
`concreteCoimageπ_desc` proves its factorization.
`concreteCoimageDesc_unique` proves uniqueness by cancellation of the
surjective quotient projection.

These explicit descents, factorization identities, and uniqueness proofs
are the fields supplied to `CokernelCofork.IsColimit.ofπ`.
`concreteCoimageCofork f` is the actual
`CokernelCofork (concreteKernelι f)` with projection `concreteCoimageπ f`,
and `concreteCoimageIsColimit f` is its `IsColimit`.
`concreteCoimageIsColimit_desc` identifies its descent with the constructed
quotient descent. `concreteCoimageDesc_self` recovers
`factorThruConcreteCoimage f` when descending `f` itself.

## Compatibility with the selected categorical objects

`cokernelConcreteKernelIsoCoimage f` compares the selected
`cokernel (concreteKernelι f)` with the constructed quotient, using the
isomorphism between the selected colimit and the explicit colimit cocone.
Let `i` denote this isomorphism, `q = concreteCoimageπ f`,
`t = factorThruConcreteCoimage f`, and
`d = cokernel.desc (concreteKernelι f) f (concreteKernelι_comp f)`.
The module proves all four identities:

```text
cokernel.π (concreteKernelι f) ≫ i.hom = q
q ≫ i.inv = cokernel.π (concreteKernelι f)
i.hom ≫ t = d
i.inv ≫ d = t.
```

Their names are `π_cokernelConcreteKernelIsoCoimage_hom`,
`π_cokernelConcreteKernelIsoCoimage_inv`,
`cokernelConcreteKernelIsoCoimage_hom_factor`, and
`cokernelConcreteKernelIsoCoimage_inv_factor`.

`coimageIsoConcrete f` compares Mathlib's `Abelian.coimage f`, defined as
`cokernel (kernel.ι f)`, with this same concrete quotient. It first applies
`cokernel.mapIso` to the published `kernelIsoConcrete f`, then composes with
`cokernelConcreteKernelIsoCoimage f`. Writing this isomorphism as `j`, its
four compatibility laws are:

```text
Abelian.coimage.π f ≫ j.hom = q
q ≫ j.inv = Abelian.coimage.π f
j.hom ≫ t = Abelian.factorThruCoimage f
j.inv ≫ Abelian.factorThruCoimage f = t.
```

These are `π_coimageIsoConcrete_hom`, `π_coimageIsoConcrete_inv`,
`coimageIsoConcrete_hom_factor`, and `coimageIsoConcrete_inv_factor`.
The descended-map identities follow by cancellation of the corresponding
epimorphic projection and the factorization laws. Both comparisons thus
retain both arrows of the factorization.

## Coimage property in the opposite category

`concreteCoimageOpMonoFactorisation f` is an actual
`Limits.MonoFactorisation f.op` with object
`Opposite.op (concreteCoimage f)`, monomorphism
`(concreteCoimageπ f).op`, and other arrow
`(factorThruConcreteCoimage f).op`. The three
`concreteCoimageOpMonoFactorisation_I`, `_m`, and `_e` laws identify these
fields definitionally.

`concreteCoimageOpIsImage f` supplies the actual `Limits.IsImage` of this
factorization. The descended original map is already proved monic, so its
opposite is epic. The published ambient abelian structure and Mathlib's
opposite-category abelianness make that opposite arrow strongly epic via
`strongEpi_of_epi`. The proof forms the resulting
`StrongEpiMonoFactorisation` and uses `toMonoIsImage`. Thus the coimage
universal property is constructed; it is not an input assumption.

## Provenance, scope, and validation

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, A.VI.2, printed p.262/PDF268, defines coimage
dually to image and identifies it with `coker(ker f)` in property 4;
property 5 gives the epi-mono factorization. The original module
conventions on printed pp.5–7/PDF11–13 allow the unrestricted actions
retained here. Registered source ID:
`renard-2026-representations-groupes-reductifs-padiques`; original SHA256:
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The explicit stable-kernel quotient, the original quotient descents, and
the compatibility laws in this module are internal derived specializations
of those categorical assertions. They reuse the published original kernel,
quotient mechanism, mono/injective criterion, and ambient abelian structure.
The defective full-subcategory closure criterion discussed in
`notes/renard/appendix-a-corrections.md` is not used.

This module does not construct the separate isomorphism from the concrete
coimage to the concrete image, prove uniqueness of arbitrary epi-mono
factorizations, or establish categorical exactness, functor exactness, or
abelianness of the nondegenerate full subcategory.

Development checks compile every one of the 39 public declarations as an
unapplied constant against its complete expected telescope, both at
independent `uA,uM` and at `(0,1)` and `(1,0)`, for 117 assignments. The
checks use the pinned Lean-service environment; inspection of
`concreteCoimageOpIsImage` retains exactly the independent `uA,uM` levels
and uses only `propext`, `Classical.choice`, and `Quot.sound`.

Worker 6 authored the initial quotient/descent/colimit draft. Worker 490
reused it and supplied the selected-object comparisons, the opposite image
universal property, complete interface checks, and final documentation.
