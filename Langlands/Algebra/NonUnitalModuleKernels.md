# Concrete kernels and cokernels of original nonunital modules

Worker 691. This is an internal derived construction in the published category
`Langlands.Algebra.NonUnitalModuleCat`. It packages the published stable additive
subgroups and quotient actions as actual categorical kernels and cokernels,
using the published pointwise zero morphisms. All actions and additive groups
are the given original structures.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original-action conventions at printed pages 5–6 / PDF pages 11–12,
I.1.2 at printed page 7 / PDF page 13, A.VI.1 at printed page 261 / PDF
page 267, and A.VI.2 properties 2–5 and its exact-sequence paragraph at
printed page 262 / PDF page 268 were read for this construction.
A.VI.1 requires kernels and cokernels in axioms AB2 and AB2*. A.VI.2 uses
them to discuss subobjects, quotients, images and exactness. Those passages
motivate the present concrete universal properties; the integer specialization
and the explicit Lean packaging are internal derived content.

The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 18–19, and the Library note
`notes/renard/appendix-a-corrections.md` were also read. The
[author's book and errata section](https://perso.pages.math.cnrs.fr/users/david.renard/)
was checked live on 30 October 2026: its bytes match the registered
`renard-author-page-2026-10-26` snapshot, and its linked 2010 errata retain
the registered fingerprint. That section links the corrected French 2026
edition and separately identifies the 2010 errata; it supplies no separate
2026 errata link. No project errata file exists for these sources.
The full-subcategory closure assertion discussed in the correction note does
not enter this construction.

## Original stable subgroup and quotient data

Let `A : Type uA` have `[NonUnitalRing A]`. The unbundled helpers in
`NonUnitalModuleHom` allow `M : Type uM`, `N : Type uN` and `P : Type uP`,
with their given additive groups and original `NonUnitalModule` actions.
All four universes are independent.

For an original intertwiner `f : NonUnitalModuleHom A M N`,
`kernelSubmodule f` and `rangeSubmodule f` are exactly
`NonUnitalSubmodule.ofIntCompatible f.toIntLinearIntertwiner.ker` and
`NonUnitalSubmodule.ofIntCompatible f.toIntLinearIntertwiner.range`.
The published canonical integer linearization preserves the original map and
action. The membership identities `mem_kernelSubmodule` and
`mem_rangeSubmodule` are respectively `f m = 0` and `∃ m, f m = n`.
They are definitional equalities.

`cokernelCarrier f` is the existing quotient
`N ⧸ f.toIntLinearIntertwiner.range.toSubmodule`, in `Type uN`.
`cokernelNonUnitalModule f` selects the published
`CompatibleSubmodule.quotientNonUnitalModule` on this carrier.
`cokernelProjection f` is the published `mkQNonUnitalModuleHom`.
`cokernelProjection_apply` evaluates it as the ordinary quotient constructor,
and `cokernel_smul_mk` identifies the action on the coset of `n` with the
coset of the given original `a • n`. The quotient is by the stable range;
`cokernelProjection_eq_zero_iff` identifies zero cosets with membership in
`rangeSubmodule f`, using `Submodule.Quotient.mk_eq_zero`.

## Concrete categorical kernel

Now take objects `M,N,P : NonUnitalModuleCat.{uA,uM} A` and `f : M ⟶ N`.
The definitions in the namespace `NonUnitalModuleCat` supply the following data.

`concreteKernel f` bundles `f.kernelSubmodule` with its existing inherited
original action. `concreteKernel_carrier` identifies its carrier with the
actual subtype of vectors sent to zero. `concreteKernelι f` is the existing
subtype inclusion. Its evaluation and inherited-action laws are
`concreteKernelι_apply` and `concreteKernel_smul_coe`.
The composite equation `concreteKernelι_comp` follows from each vector's
subtype property and the published pointwise zero morphism.
Categorical evaluation formulas use `NonUnitalModuleHom.toAddMonoidHom`
explicitly to expose the original underlying map.

Given `g : P ⟶ M` with `h : g ≫ f = 0`, `concreteKernelLift f g h`
uses the unbundled `kernelLift`, whose value at `p` is exactly
`⟨g p, _⟩`. The vanishing proof is obtained by evaluating `h` at `p`.
The lift retains additivity and the original action by subtype extensionality
applied to the corresponding laws of `g`.
`concreteKernelLift_apply_coe` gives its underlying value,
`concreteKernelLift_ι` proves its factorization, and
`concreteKernelLift_unique` proves uniqueness by evaluating the assumed
factorization and using subtype extensionality.

`concreteKernelFork f` is `KernelFork.ofι` on this actual inclusion.
`concreteKernelIsLimit f` constructs `KernelFork.IsLimit.ofι` from the
explicit lift, factorization and uniqueness just described.
`concreteKernelIsLimit_lift` identifies the constructed limit's lift with
`concreteKernelLift` definitionally. No kernel witness is an input.

## Concrete categorical cokernel

`concreteCokernel f` bundles `f.cokernelCarrier` with exactly
`f.cokernelNonUnitalModule`. Its carrier identity is
`concreteCokernel_carrier`. `concreteCokernelπ f` is exactly the existing
quotient projection. Its coset evaluation, original-action evaluation and
vanishing criterion are `concreteCokernelπ_apply`,
`concreteCokernel_smul_mk` and `concreteCokernelπ_eq_zero_iff`.
`comp_concreteCokernelπ` follows because `f m` belongs to the actual range.

Given `g : N ⟶ P` with `h : f ≫ g = 0`, evaluating `h` shows
`f.toIntLinearIntertwiner.range ≤ g.toIntLinearIntertwiner.ker`.
The helper `range_le_ker_of_comp_eq_zero` records this inclusion.
The unbundled `cokernelDesc f g h` then calls the published integer-compatible
`LinearIntertwiner.liftQ` and forgets only its integer linearity with
`toNonUnitalModuleHom`. Its target still has the given original action.
`concreteCokernelDesc f g h` is this same map in the original category.
`concreteCokernelDesc_apply_mk` gives its value `g n` on a coset represented
by `n`; `concreteCokernelπ_desc` gives the factorization.
`concreteCokernelDesc_unique` uses quotient induction and evaluation of the
assumed factorization on representatives.

`concreteCokernelCofork f` is `CokernelCofork.ofπ` on this projection.
`concreteCokernelIsColimit f` constructs `CokernelCofork.IsColimit.ofπ`
using the explicit descent and its two laws.
`concreteCokernelIsColimit_desc` identifies its descent with
`concreteCokernelDesc` definitionally. No cokernel witness is an input.

## Selected objects and their maps

The named instances `hasKernels` and `hasCokernels` supply downstream
inference with these constructed universal properties. The comparisons
`kernelIsoConcrete f` and `cokernelIsoConcrete f` use the usual uniqueness
isomorphisms for selected limits and colimits. They also identify the maps:

```lean
(kernelIsoConcrete f).inv ≫ kernel.ι f = concreteKernelι f
(kernelIsoConcrete f).hom ≫ concreteKernelι f = kernel.ι f
cokernel.π f ≫ (cokernelIsoConcrete f).hom = concreteCokernelπ f
concreteCokernelπ f ≫ (cokernelIsoConcrete f).inv = cokernel.π f
```

These are `kernelIsoConcrete_inv_ι`, `kernelIsoConcrete_hom_ι`,
`π_cokernelIsoConcrete_hom` and `π_cokernelIsoConcrete_inv`, respectively.
They follow from Mathlib's selected-limit and selected-colimit comparison
identities. Only these comparison isomorphisms are declared noncomputable.

## Size, verification and scope

Private development checks assign complete unapplied types to the seven main
unbundled helpers, retaining independent scalar, source, target and auxiliary
carrier universes. They assign complete unapplied types to the bundled
objects, inclusion/projection, lift/descent, fork/cofork, universal properties,
instances and selected-object isomorphisms, with independent `uA,uM`.
Every one of those categorical signatures is also checked at `(0,1)` and
`(1,0)`, including instance inference. The resulting carriers remain in
`Type uM`; the category's larger object universe does not enlarge them.
All 50 named declarations have axiom reports containing only Lean's standard
`propext`, `Classical.choice` and `Quot.sound`, where needed.
These development checks do not constitute independent semantic acceptance.

The hypotheses permit arbitrary nonunital rings, zero rings, zero carriers,
and zero original actions over unital rings. There is no original unit law,
idempotentedness, nondegeneracy, nontriviality, scalar field or finiteness
hypothesis. The construction assumes neither ambient abelianness nor an
original-category kernel or cokernel. Ambient abelianness, images/coimages,
exactness and integer-unitization comparisons, the nondegenerate subcategory,
scalar Hom spaces, tensors and adjoints remain separate obligations.
